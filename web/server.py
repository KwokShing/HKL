# -*- coding: utf-8 -*-
from __future__ import annotations

import ast
import atexit
import hashlib
import importlib.util
import inspect
import json
import multiprocessing as mp
import os
import re
import secrets
import sys
import threading
import traceback
from functools import partial
from html import unescape
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from itertools import zip_longest
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, quote, urljoin, urlsplit

import requests
import urllib3

REPO_ROOT = Path(__file__).resolve().parents[1]
PY_DIR = (REPO_ROOT / "py").resolve()
WEB_DIR = Path(__file__).resolve().parent
CACHE_DIR = WEB_DIR / ".cache"
HOST = "127.0.0.1"
PORT = 8000
CALL_TIMEOUT = 45
MEDIA_PROXY_LIMIT = 8192

_MEDIA_TARGETS: dict[str, tuple[str, dict[str, str]]] = {}
_MEDIA_TARGETS_LOCK = threading.Lock()
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

sys.path.insert(0, str(REPO_ROOT))


class PluginError(RuntimeError):
    pass


class PluginTimeout(PluginError):
    pass


def _safe_plugin_path(file_name: str) -> Path:
    candidate = (PY_DIR / file_name).resolve()
    if candidate.parent != PY_DIR or candidate.suffix.lower() != ".py" or not candidate.is_file():
        raise PluginError("插件不存在或路径无效")
    return candidate

def discover_plugins() -> list[dict[str, Any]]:
    import warnings

    plugins = []
    for path in sorted(PY_DIR.glob("*.py"), key=lambda item: item.name.casefold()):
        methods: set[str] = set()
        imports: set[str] = set()
        error = ""
        try:
            source = path.read_text(encoding="utf-8-sig", errors="replace")
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", SyntaxWarning)
                tree = ast.parse(source, filename=str(path))
            for node in ast.walk(tree):
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    methods.add(node.name)
                elif isinstance(node, ast.Import):
                    imports.update(item.name.split(".")[0] for item in node.names)
                elif isinstance(node, ast.ImportFrom) and node.module:
                    imports.add(node.module.split(".")[0])
        except (OSError, SyntaxError) as exc:
            error = f"{type(exc).__name__}: {exc}"
        missing = []
        for name in sorted(imports):
            if name in sys.stdlib_module_names or name == "base":
                continue
            try:
                available = importlib.util.find_spec(name) is not None
            except (ImportError, AttributeError, ValueError):
                available = False
            if not available:
                missing.append(name)
        plugins.append(
            {
                "id": path.name,
                "name": path.stem,
                "methods": sorted(
                    methods & {"homeContent", "categoryContent", "searchContent", "detailContent", "playerContent"}
                ),
                "missing": missing,
                "error": error,
            }
        )
    return plugins


def _invoke(instance: Any, method_name: str, candidates: list[tuple[Any, ...]]) -> Any:
    method = getattr(instance, method_name, None)
    if not callable(method):
        raise PluginError(f"插件没有实现 {method_name}")
    signature = inspect.signature(method)
    for args in candidates:
        try:
            signature.bind(*args)
        except TypeError:
            continue
        return method(*args)
    raise PluginError(f"{method_name} 的参数签名不兼容：{signature}")


def _worker_main(connection: Any, plugin_path: str, site_id: str, base_url: str) -> None:
    try:
        import warnings

        os.environ["HKL_CACHE_DIR"] = str(CACHE_DIR)
        os.environ["HKL_PROXY_URL"] = (
            f"{base_url}/api/local-proxy?site={quote(site_id, safe='')}"
        )
        os.chdir(REPO_ROOT)
        sys.path.insert(0, str(REPO_ROOT))

        # 部分旧插件直接调用 requests 且未设置 timeout，避免 worker 永久阻塞。
        original_request = requests.sessions.Session.request
        import_in_progress = True

        def request_with_default_timeout(session: Any, *args: Any, **kwargs: Any) -> Any:
            method = str(args[0] if args else kwargs.get("method", "GET")).upper()
            url = str(args[1] if len(args) > 1 else kwargs.get("url", ""))
            if kwargs.get("timeout") is None:
                kwargs["timeout"] = 5 if import_in_progress else 20
            try:
                return original_request(session, *args, **kwargs)
            except requests.RequestException as exc:
                if not import_in_progress or method != "GET":
                    raise
                print(f"[{site_id}] 导入阶段 GET 失败，使用空响应继续加载：{exc}", flush=True)
                response = requests.Response()
                response.status_code = 599
                response.url = url
                response.reason = str(exc)
                response._content = b""
                return response

        requests.sessions.Session.request = request_with_default_timeout
        module_name = "hkl_plugin_" + hashlib.sha256(plugin_path.encode("utf-8")).hexdigest()[:20]
        spec = importlib.util.spec_from_file_location(module_name, plugin_path)
        if spec is None or spec.loader is None:
            raise PluginError("无法创建插件模块")
        module = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = module
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", SyntaxWarning)
                spec.loader.exec_module(module)
        finally:
            import_in_progress = False
        spider_class = getattr(module, "Spider", None)
        if spider_class is None:
            raise PluginError("插件没有 Spider 类")
        instance = spider_class()
        plugin_cache_dir = CACHE_DIR / "plugins" / hashlib.sha256(site_id.encode("utf-8")).hexdigest()[:20]
        for attribute in dir(instance):
            if not attribute.endswith("_cache_file"):
                continue
            try:
                cache_path = Path(getattr(instance, attribute))
                if cache_path.parent.resolve() != PY_DIR:
                    continue
                plugin_cache_dir.mkdir(parents=True, exist_ok=True)
                setattr(instance, attribute, str(plugin_cache_dir / cache_path.name))
            except (OSError, TypeError, ValueError):
                continue
        init_method = getattr(instance, "init", None)
        if callable(init_method):
            _invoke(instance, "init", [("",), ()])
        connection.send({"ok": True, "ready": True})
    except Exception as exc:
        connection.send({"ok": False, "error": f"插件加载失败：{type(exc).__name__}: {exc}"})
        connection.close()
        return

    while True:
        try:
            message = connection.recv()
            operation = message.get("operation")
            data = message.get("data", {})
            if operation == "stop":
                break
            if operation == "home":
                result = _invoke(instance, "homeContent", [(False,), ()])
            elif operation == "category":
                result = _invoke(instance, "categoryContent", [
                    (data["tid"], str(data["page"]), False, data.get("extend", {})),
                    (data["tid"], str(data["page"]), False),
                    (data["tid"], str(data["page"])),
                ])
            elif operation == "search":
                result = _invoke(instance, "searchContent", [
                    (data["keyword"], False, str(data["page"])),
                    (data["keyword"], False),
                    (data["keyword"],),
                ])
            elif operation == "detail":
                result = _invoke(instance, "detailContent", [([data["vod_id"]],), (data["vod_id"],)])
            elif operation == "player":
                result = _invoke(instance, "playerContent", [
                    (data.get("flag", ""), data["vid"], []),
                    (data.get("flag", ""), data["vid"], None),
                    (data.get("flag", ""), data["vid"]),
                    (data["vid"],),
                ])
            elif operation == "local_proxy":
                result = _invoke(instance, "localProxy", [(data,)])
            else:
                raise PluginError("未知插件操作")
            connection.send({"ok": True, "result": result})
        except EOFError:
            break
        except Exception as exc:
            connection.send({
                "ok": False,
                "error": f"{type(exc).__name__}: {exc}",
                "traceback": traceback.format_exc(limit=5),
            })
    try:
        destroy = getattr(instance, "destroy", None)
        if callable(destroy):
            destroy()
    finally:
        connection.close()


class PluginRuntime:
    def __init__(self, path: Path, site_id: str, base_url: str) -> None:
        self.path = path
        self.site_id = site_id
        self.base_url = base_url
        self.modified = path.stat().st_mtime_ns
        self.process: Any = None
        self.connection: Any = None
        self.lock = threading.Lock()

    def _start(self) -> None:
        context = mp.get_context("spawn")
        parent, child = context.Pipe()
        process = context.Process(
            target=_worker_main,
            args=(child, str(self.path), self.site_id, self.base_url),
            daemon=True,
        )
        process.start()
        child.close()
        if not parent.poll(CALL_TIMEOUT):
            process.terminate()
            process.join(timeout=2)
            parent.close()
            raise PluginTimeout("插件加载超时")
        ready = parent.recv()
        if not ready.get("ok"):
            process.join(timeout=2)
            parent.close()
            raise PluginError(ready.get("error") or "插件加载失败")
        self.process = process
        self.connection = parent

    def call(self, operation: str, data: dict[str, Any]) -> Any:
        with self.lock:
            if self.path.stat().st_mtime_ns != self.modified:
                self.close()
                self.modified = self.path.stat().st_mtime_ns
            if self.process is None or not self.process.is_alive():
                self.close()
                self._start()
            self.connection.send({"operation": operation, "data": data})
            if not self.connection.poll(CALL_TIMEOUT):
                self.close()
                raise PluginTimeout(f"{operation} 调用超过 {CALL_TIMEOUT} 秒")
            response = self.connection.recv()
            if not response.get("ok"):
                raise PluginError(response.get("error") or "插件调用失败")
            return response.get("result")

    def close(self) -> None:
        connection, process = self.connection, self.process
        self.connection = None
        self.process = None
        if connection is not None:
            try:
                if process is not None and process.is_alive():
                    connection.send({"operation": "stop", "data": {}})
            except (BrokenPipeError, EOFError, OSError):
                pass
            connection.close()
        if process is not None:
            process.join(timeout=1)
            if process.is_alive():
                process.terminate()
                process.join(timeout=2)


_RUNTIMES: dict[str, PluginRuntime] = {}
_RUNTIMES_LOCK = threading.Lock()


def get_runtime(site_id: str) -> PluginRuntime:
    path = _safe_plugin_path(site_id)
    with _RUNTIMES_LOCK:
        runtime = _RUNTIMES.get(site_id)
        if runtime is None:
            runtime = PluginRuntime(path, site_id, f"http://{HOST}:{PORT}")
            _RUNTIMES[site_id] = runtime
        return runtime


def close_runtimes() -> None:
    with _RUNTIMES_LOCK:
        for runtime in _RUNTIMES.values():
            runtime.close()
        _RUNTIMES.clear()


atexit.register(close_runtimes)


def clean_text(value: Any) -> str:
    text = re.sub(r"<[^>]*>", "", str(value or ""))
    return unescape(text).strip()


def normalize_videos(value: Any) -> list[dict[str, Any]]:
    videos = []
    for item in value if isinstance(value, list) else []:
        if not isinstance(item, dict):
            continue
        videos.append({
            "vod_id": item.get("vod_id", item.get("id")),
            "vod_name": item.get("vod_name") or item.get("name") or "未知名称",
            "vod_pic": item.get("vod_pic") or item.get("pic") or "",
            "vod_remarks": item.get("vod_remarks") or item.get("remarks") or "",
            "vod_year": item.get("vod_year") or "",
            "type_name": item.get("type_name") or item.get("vod_class") or "",
        })
    return videos


def normalize_home(result: Any) -> dict[str, Any]:
    if not isinstance(result, dict):
        raise PluginError("homeContent 没有返回字典")
    categories = []
    for item in result.get("class", []):
        if isinstance(item, dict):
            type_id = item.get("type_id", item.get("id"))
            type_name = item.get("type_name", item.get("name"))
            if type_id is not None and type_name:
                categories.append({"type_id": str(type_id), "type_name": str(type_name)})
    return {"categories": categories, "items": normalize_videos(result.get("list"))}


def normalize_listing(result: Any, requested_page: int) -> dict[str, Any]:
    if not isinstance(result, dict):
        raise PluginError("插件列表接口没有返回字典")
    items = normalize_videos(result.get("list"))
    try:
        page = int(result.get("page", requested_page))
    except (TypeError, ValueError):
        page = requested_page
    try:
        page_count = int(result.get("pagecount", result.get("pageCount", page)))
    except (TypeError, ValueError):
        page_count = page
    has_more = page_count > page
    if "pagecount" not in result and "pageCount" not in result:
        try:
            limit = int(result.get("limit", 0))
        except (TypeError, ValueError):
            limit = 0
        has_more = bool(limit and len(items) >= limit)
    return {"items": items, "page": page, "has_more": has_more}


def normalize_detail(result: Any) -> dict[str, Any]:
    if not isinstance(result, dict) or not isinstance(result.get("list"), list) or not result["list"]:
        raise PluginError("详情接口没有返回影片")
    video = result["list"][0]
    if not isinstance(video, dict):
        raise PluginError("详情数据格式错误")
    source_names = str(video.get("vod_play_from") or "").split("$$$")
    source_values = str(video.get("vod_play_url") or "").split("$$$")
    sources = []
    for index, (name, play_list) in enumerate(zip_longest(source_names, source_values, fillvalue="")):
        episodes = []
        for entry in str(play_list).split("#"):
            if not entry:
                continue
            if "$" in entry:
                episode_name, vid = entry.split("$", 1)
            else:
                episode_name, vid = f"播放 {len(episodes) + 1}", entry
            if vid:
                episodes.append({"name": episode_name or f"第 {len(episodes) + 1} 集", "vid": vid})
        if episodes:
            sources.append({"name": name or f"片源 {index + 1}", "flag": name, "episodes": episodes})
    return {
        "vod_id": video.get("vod_id"),
        "vod_name": video.get("vod_name") or "未知名称",
        "vod_pic": video.get("vod_pic") or "",
        "vod_remarks": video.get("vod_remarks") or "",
        "vod_year": video.get("vod_year") or "",
        "vod_area": video.get("vod_area") or "",
        "vod_actor": video.get("vod_actor") or "",
        "vod_director": video.get("vod_director") or "",
        "type_name": video.get("type_name") or video.get("vod_class") or "",
        "vod_content": clean_text(video.get("vod_content")),
        "sources": sources,
    }


def normalize_player(result: Any) -> dict[str, Any]:
    if not isinstance(result, dict):
        raise PluginError("playerContent 没有返回字典")
    raw_url = result.get("url")
    options = []
    if isinstance(raw_url, list):
        for index in range(0, len(raw_url) - 1, 2):
            options.append({"name": str(raw_url[index]), "url": str(raw_url[index + 1])})
        raw_url = next((item["url"] for item in options if item["url"].startswith(("http://", "https://"))), "")
    url = str(raw_url or "")
    if not url.startswith(("http://", "https://")):
        if result.get("parse") or result.get("jx"):
            raise PluginError("该片源需要 TVBox 外部解析，浏览器无法直接播放")
        raise PluginError("插件没有返回可直接播放的 HTTP 地址")
    headers = result.get("header") if isinstance(result.get("header"), dict) else {}
    return {"url": url, "options": options, "headers": headers}


def register_media_target(url: str, headers: dict[str, Any], manifest: bool = False) -> str:
    if not url.startswith(("http://", "https://")):
        return url
    blocked_headers = {"connection", "content-length", "host", "proxy-authorization", "transfer-encoding"}
    safe_headers = {
        str(name): str(value)
        for name, value in headers.items()
        if str(name).lower() not in blocked_headers and "\r" not in str(value) and "\n" not in str(value)
    }
    token = secrets.token_urlsafe(24)
    with _MEDIA_TARGETS_LOCK:
        if len(_MEDIA_TARGETS) >= MEDIA_PROXY_LIMIT:
            for old_token in list(_MEDIA_TARGETS)[:1024]:
                _MEDIA_TARGETS.pop(old_token, None)
        _MEDIA_TARGETS[token] = (url, safe_headers)
    suffix = "&format=.m3u8" if manifest else ""
    return f"/api/media-proxy?token={quote(token, safe='')}{suffix}"


def get_media_target(token: str) -> tuple[str, dict[str, str]] | None:
    with _MEDIA_TARGETS_LOCK:
        return _MEDIA_TARGETS.get(token)


def rewrite_media_manifest(text: str, base_url: str, headers: dict[str, str]) -> str:
    def proxy_url(value: str) -> str:
        target = urljoin(base_url, value)
        return register_media_target(target, headers) if target.startswith(("http://", "https://")) else value

    output = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("#"):
            output.append(proxy_url(stripped))
            continue
        if 'URI="' in line:
            line = re.sub(r'URI="([^"]+)"', lambda match: f'URI="{proxy_url(match.group(1))}"', line)
        output.append(line)
    return "\n".join(output) + "\n"


def unwrap_png_transport_stream(data: bytes) -> bytes | None:
    if not data.startswith(b"\x89PNG\r\n\x1a\n"):
        return None
    position = 8
    while position + 12 <= len(data):
        length = int.from_bytes(data[position:position + 4], "big")
        chunk_type = data[position + 4:position + 8]
        chunk_end = position + 12 + length
        if chunk_end > len(data):
            return None
        if chunk_type == b"IEND":
            payload = data[chunk_end:]
            search_limit = min(max(len(payload) - 564, 0), 4096)
            for offset in range(search_limit + 1):
                if all(payload[offset + step] == 0x47 for step in (0, 188, 376)):
                    transport_stream = payload[offset:]
                    complete_length = len(transport_stream) // 188 * 188
                    return transport_stream[:complete_length] if complete_length else None
            return None
        position = chunk_end
    return None


class Handler(SimpleHTTPRequestHandler):
    server_version = "HKLRenderer/1.0"

    def do_GET(self) -> None:
        parsed = urlsplit(self.path)
        params = parse_qs(parsed.query, keep_blank_values=True)
        routes = {
            "/api/plugins": self.api_plugins,
            "/api/home": self.api_home,
            "/api/category": self.api_category,
            "/api/search": self.api_search,
            "/api/detail": self.api_detail,
            "/api/player": self.api_player,
            "/api/media-proxy": self.api_media_proxy,
            "/api/local-proxy": self.api_local_proxy,
        }
        route = routes.get(parsed.path)
        if route:
            route(params)
            return
        if parsed.path.startswith("/api/"):
            self.send_json(404, {"error": "未知 API"})
            return
        super().do_GET()

    def end_headers(self) -> None:
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        super().end_headers()

    def first(self, params: dict[str, list[str]], name: str) -> str:
        values = params.get(name, [])
        return str(values[0]).strip() if values else ""

    def require_site(self, params: dict[str, list[str]]) -> str | None:
        site = self.first(params, "site")
        if not site:
            self.send_json(400, {"error": "缺少 site"})
            return None
        try:
            _safe_plugin_path(site)
        except PluginError as exc:
            self.send_json(404, {"error": str(exc)})
            return None
        return site

    def page_number(self, params: dict[str, list[str]]) -> int | None:
        try:
            page = int(self.first(params, "page") or "1")
        except ValueError:
            page = 0
        if page < 1 or page > 10000:
            self.send_json(400, {"error": "页码无效"})
            return None
        return page

    def call_plugin(self, site: str, operation: str, data: dict[str, Any]) -> Any:
        try:
            return get_runtime(site).call(operation, data)
        except PluginTimeout as exc:
            self.send_json(504, {"error": str(exc)})
        except PluginError as exc:
            self.send_json(502, {"error": str(exc)})
        except (EOFError, BrokenPipeError, OSError) as exc:
            self.send_json(502, {"error": f"插件 worker 异常：{exc}"})
        return None

    def api_plugins(self, _params: dict[str, list[str]]) -> None:
        self.send_json(200, {"plugins": discover_plugins()})

    def api_home(self, params: dict[str, list[str]]) -> None:
        site = self.require_site(params)
        if site is None:
            return
        result = self.call_plugin(site, "home", {})
        if result is None:
            return
        try:
            self.send_json(200, normalize_home(result))
        except PluginError as exc:
            self.send_json(502, {"error": str(exc)})

    def api_category(self, params: dict[str, list[str]]) -> None:
        site, page = self.require_site(params), self.page_number(params)
        tid = self.first(params, "type_id")
        if site is None or page is None:
            return
        if not tid:
            self.send_json(400, {"error": "缺少 type_id"})
            return
        result = self.call_plugin(site, "category", {"tid": tid, "page": page, "extend": {}})
        if result is None:
            return
        try:
            self.send_json(200, normalize_listing(result, page))
        except PluginError as exc:
            self.send_json(502, {"error": str(exc)})

    def api_search(self, params: dict[str, list[str]]) -> None:
        site, page = self.require_site(params), self.page_number(params)
        keyword = self.first(params, "wd")
        if site is None or page is None:
            return
        if not keyword or len(keyword) > 100:
            self.send_json(400, {"error": "搜索词无效"})
            return
        result = self.call_plugin(site, "search", {"keyword": keyword, "page": page})
        if result is None:
            return
        try:
            self.send_json(200, normalize_listing(result, page))
        except PluginError as exc:
            self.send_json(502, {"error": str(exc)})

    def api_detail(self, params: dict[str, list[str]]) -> None:
        site = self.require_site(params)
        vod_id = self.first(params, "vod_id")
        if site is None:
            return
        if not vod_id:
            self.send_json(400, {"error": "缺少 vod_id"})
            return
        result = self.call_plugin(site, "detail", {"vod_id": vod_id})
        if result is None:
            return
        try:
            self.send_json(200, normalize_detail(result))
        except PluginError as exc:
            self.send_json(502, {"error": str(exc)})

    def api_player(self, params: dict[str, list[str]]) -> None:
        site = self.require_site(params)
        vid = self.first(params, "vid")
        if site is None:
            return
        if not vid:
            self.send_json(400, {"error": "缺少 vid"})
            return
        result = self.call_plugin(site, "player", {"flag": self.first(params, "flag"), "vid": vid})
        if result is None:
            return
        try:
            player = normalize_player(result)
            if re.search(r"\.m3u8(?:$|[?#])", player["url"], re.I):
                player["url"] = register_media_target(player["url"], player["headers"], manifest=True)
                player["proxied"] = True
            self.send_json(200, player)
        except PluginError as exc:
            self.send_json(422, {"error": str(exc)})

    def api_media_proxy(self, params: dict[str, list[str]]) -> None:
        token = self.first(params, "token")
        target = get_media_target(token)
        if target is None:
            self.send_json(404, {"error": "媒体代理地址已失效，请重新选择剧集"})
            return
        url, headers = target
        request_headers = dict(headers)
        range_header = self.headers.get("Range")
        image_path = urlsplit(url).path.lower()
        image_wrapped_candidate = bool(re.search(r"\.(?:png|jpe?g|webp|gif)$", image_path))
        if range_header and not image_wrapped_candidate:
            request_headers["Range"] = range_header
        try:
            response = requests.get(
                url,
                headers=request_headers,
                timeout=30,
                verify=False,
                allow_redirects=True,
            )
        except requests.RequestException as exc:
            self.send_json(502, {"error": f"媒体请求失败：{exc}"})
            return

        body = response.content
        status = response.status_code
        content_type = response.headers.get("Content-Type") or "application/octet-stream"
        final_image_path = urlsplit(response.url).path.lower()
        partial_image_candidate = status == 206 and range_header and (
            content_type.lower().startswith("image/")
            or bool(re.search(r"\.(?:png|jpe?g|webp|gif)$", final_image_path))
        )
        if partial_image_candidate:
            try:
                full_response = requests.get(
                    url,
                    headers=dict(headers),
                    timeout=30,
                    verify=False,
                    allow_redirects=True,
                )
                if full_response.ok:
                    response = full_response
                    body = response.content
                    status = response.status_code
                    content_type = response.headers.get("Content-Type") or "application/octet-stream"
            except requests.RequestException:
                pass
        transformed = False
        if body.lstrip(b"\xef\xbb\xbf \t\r\n").startswith(b"#EXTM3U"):
            manifest = rewrite_media_manifest(body.decode("utf-8-sig", errors="replace"), response.url, headers)
            body = manifest.encode("utf-8")
            content_type = "application/vnd.apple.mpegurl; charset=utf-8"
            transformed = True
        else:
            transport_stream = unwrap_png_transport_stream(body)
            if transport_stream is not None:
                body = transport_stream
                status = 200
                content_type = "video/mp2t"
                transformed = True

        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        if not transformed:
            for name in ("Accept-Ranges", "Content-Range"):
                value = response.headers.get(name)
                if value:
                    self.send_header(name, value)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def api_local_proxy(self, params: dict[str, list[str]]) -> None:
        site = self.require_site(params)
        if site is None:
            return
        proxy_params = {key: values[0] if len(values) == 1 else values for key, values in params.items() if key != "site"}
        result = self.call_plugin(site, "local_proxy", proxy_params)
        if result is None:
            return
        if not isinstance(result, (list, tuple)) or len(result) < 3:
            self.send_json(502, {"error": "localProxy 返回格式错误"})
            return
        try:
            status = int(result[0])
        except (TypeError, ValueError):
            status = 200
        content_type = str(result[1] or "application/octet-stream")
        content = result[2]
        if isinstance(content, bytes):
            body = content
        elif isinstance(content, bytearray):
            body = bytes(content)
        elif isinstance(content, list) and all(isinstance(item, int) for item in content):
            body = bytes(content)
        else:
            body = str(content or "").encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, status: int, data: Any) -> None:
        body = json.dumps(data, ensure_ascii=False, default=str).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


if __name__ == "__main__":
    mp.freeze_support()
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    handler = partial(Handler, directory=str(WEB_DIR))
    address = (HOST, PORT)
    print(f"HKL 本地网页：http://{HOST}:{PORT}")
    print(f"插件目录：{PY_DIR}")
    try:
        ThreadingHTTPServer(address, handler).serve_forever()
    except KeyboardInterrupt:
        print("\n服务已停止")
    finally:
        close_runtimes()
