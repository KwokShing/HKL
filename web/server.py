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
import time
import traceback
import xml.etree.ElementTree as ET
from functools import partial
from html import unescape
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from itertools import zip_longest
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, quote, unquote, urljoin, urlsplit, urlunsplit

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

_MEDIA_TARGETS: dict[str, tuple[str, dict[str, str], str]] = {}
_MEDIA_TARGETS_LOCK = threading.Lock()
_PLUGIN_DISCOVERY_LOCK = threading.Lock()
_PLUGIN_DISCOVERY_SIGNATURE: tuple[tuple[str, int, int], ...] = ()
_PLUGIN_DISCOVERY_RESULT: list[dict[str, Any]] | None = None
_RESULT_CACHE_LOCK = threading.Lock()
_RESULT_CACHE: dict[tuple[str, int, str, str], tuple[float, Any]] = {}
_RESULT_CACHE_LIMIT = 1024
HOME_CACHE_TTL = 600
CATEGORY_CACHE_TTL = 180
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

def _scan_plugins() -> list[dict[str, Any]]:
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
                "modified": str(path.stat().st_mtime_ns),
                "methods": sorted(
                    methods & {"homeContent", "categoryContent", "searchContent", "detailContent", "playerContent"}
                ),
                "missing": missing,
                "error": error,
            }
        )
    return plugins


def _plugin_directory_signature() -> tuple[tuple[str, int, int], ...]:
    entries = []
    for path in sorted(PY_DIR.glob("*.py"), key=lambda item: item.name.casefold()):
        try:
            stat = path.stat()
        except OSError:
            continue
        entries.append((path.name, stat.st_mtime_ns, stat.st_size))
    return tuple(entries)


def discover_plugins() -> list[dict[str, Any]]:
    global _PLUGIN_DISCOVERY_RESULT, _PLUGIN_DISCOVERY_SIGNATURE

    signature = _plugin_directory_signature()
    cache_path = CACHE_DIR / "plugin-discovery.json"
    with _PLUGIN_DISCOVERY_LOCK:
        if _PLUGIN_DISCOVERY_RESULT is not None and signature == _PLUGIN_DISCOVERY_SIGNATURE:
            return _PLUGIN_DISCOVERY_RESULT
        try:
            payload = json.loads(cache_path.read_text(encoding="utf-8"))
            cached_signature = tuple(
                (str(item[0]), int(item[1]), int(item[2]))
                for item in payload.get("signature", [])
            )
            cached_plugins = payload.get("plugins")
            if (
                cached_signature == signature
                and isinstance(cached_plugins, list)
                and all(
                    isinstance(plugin, dict) and isinstance(plugin.get("modified"), str)
                    for plugin in cached_plugins
                )
            ):
                _PLUGIN_DISCOVERY_SIGNATURE = signature
                _PLUGIN_DISCOVERY_RESULT = cached_plugins
                print(f"[plugins] disk cache hit {len(cached_plugins)}", flush=True)
                return cached_plugins
        except (OSError, TypeError, ValueError):
            pass

        started = time.perf_counter()
        plugins = _scan_plugins()
        _PLUGIN_DISCOVERY_SIGNATURE = _plugin_directory_signature()
        _PLUGIN_DISCOVERY_RESULT = plugins
        try:
            CACHE_DIR.mkdir(parents=True, exist_ok=True)
            cache_path.write_text(json.dumps({
                "signature": _PLUGIN_DISCOVERY_SIGNATURE,
                "plugins": plugins,
            }, ensure_ascii=False), encoding="utf-8")
        except OSError:
            pass
        print(f"[plugins] 扫描 {len(plugins)} 个插件，用时 {(time.perf_counter() - started) * 1000:.0f}ms", flush=True)
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


def get_cached_plugin_result(site: str, operation: str, data: dict[str, Any], ttl: int) -> Any:
    path = _safe_plugin_path(site)
    signature = path.stat().st_mtime_ns
    data_key = json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    key = (site, signature, operation, data_key)
    now = time.monotonic()
    with _RESULT_CACHE_LOCK:
        cached = _RESULT_CACHE.get(key)
        if cached is not None and cached[0] > now:
            print(f"[cache] hit {operation} {site}", flush=True)
            return cached[1]
        if cached is not None:
            _RESULT_CACHE.pop(key, None)

    started = time.perf_counter()
    result = get_runtime(site).call(operation, data)
    with _RESULT_CACHE_LOCK:
        expired = [cache_key for cache_key, (expires, _) in _RESULT_CACHE.items() if expires <= now]
        for cache_key in expired:
            _RESULT_CACHE.pop(cache_key, None)
        while len(_RESULT_CACHE) >= _RESULT_CACHE_LIMIT:
            _RESULT_CACHE.pop(next(iter(_RESULT_CACHE)))
        _RESULT_CACHE[key] = (time.monotonic() + ttl, result)
    print(f"[cache] store {operation} {site} {(time.perf_counter() - started) * 1000:.0f}ms", flush=True)
    return result


def close_runtimes() -> None:
    with _RUNTIMES_LOCK:
        for runtime in _RUNTIMES.values():
            runtime.close()
        _RUNTIMES.clear()
    with _RESULT_CACHE_LOCK:
        _RESULT_CACHE.clear()


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


def media_url_candidates(url: str) -> list[str]:
    candidates = [url]
    for candidate in list(candidates):
        try:
            for values in parse_qs(urlsplit(candidate).query).values():
                candidates.extend(value for value in values if value not in candidates)
        except ValueError:
            continue
    return candidates


def is_hls_url(url: str) -> bool:
    return any(re.search(r"\.m3u8(?:$|[?&#])", candidate, re.I) for candidate in media_url_candidates(url))


def is_dash_url(url: str) -> bool:
    return any(re.search(r"\.mpd(?:$|[?&#])", candidate, re.I) for candidate in media_url_candidates(url))


def is_direct_media_url(url: str) -> bool:
    if is_hls_url(url) or is_dash_url(url):
        return True
    return any(
        re.search(r"\.(?:mp4|m4v|webm|flv|mkv|ts)(?:$|[?&#])", candidate, re.I)
        for candidate in media_url_candidates(url)
    )


def youku_embed_url(url: str) -> str:
    try:
        parsed = urlsplit(url)
    except ValueError:
        return ""
    if not (parsed.hostname or "").lower().endswith("youku.com"):
        return ""
    video_id = next(iter(parse_qs(parsed.query).get("vid", [])), "")
    if not video_id:
        match = re.search(r"/(?:id_|embed/)([A-Za-z0-9_=-]+)", parsed.path, re.I)
        video_id = match.group(1) if match else ""
    if not re.fullmatch(r"[A-Za-z0-9_=-]+", video_id):
        return ""
    return f"https://player.youku.com/embed/{quote(video_id, safe='=_-')}"


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
    requires_parse = bool(result.get("parse") or result.get("jx"))
    embed_url = youku_embed_url(url) if requires_parse else ""
    if embed_url:
        return {
            "url": embed_url,
            "source_url": url,
            "mode": "embed",
            "is_hls": False,
            "is_dash": False,
            "options": options,
            "headers": {},
        }
    if requires_parse and not is_direct_media_url(url):
        raise PluginError("该片源返回的是平台网页，需要 TVBox 外部解析；请选择其他片源")
    return {
        "url": url,
        "mode": "media",
        "is_hls": is_hls_url(url),
        "is_dash": is_dash_url(url),
        "options": options,
        "headers": headers,
    }


def register_media_target(url: str, headers: dict[str, Any], kind: str = "media") -> str:
    if not url.startswith(("http://", "https://")):
        return url
    if kind not in {"manifest", "dash_manifest", "dash_media", "segment", "map", "key", "media"}:
        kind = "media"
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
        _MEDIA_TARGETS[token] = (url, safe_headers, kind)
    if kind == "dash_media":
        return f"/api/dash-media/{quote(token, safe='')}/"
    suffix = "&format=.m3u8" if kind == "manifest" else "&format=.mpd" if kind == "dash_manifest" else ""
    return f"/api/media-proxy?token={quote(token, safe='')}{suffix}"


def get_media_target(token: str) -> tuple[str, dict[str, str], str] | None:
    with _MEDIA_TARGETS_LOCK:
        return _MEDIA_TARGETS.get(token)


def _dash_directory_url(url: str) -> str:
    parsed = urlsplit(url)
    directory = parsed.path.rsplit("/", 1)[0] + "/"
    return urlunsplit((parsed.scheme, parsed.netloc, directory, parsed.query, ""))


def _proxy_absolute_dash_value(value: str, headers: dict[str, str]) -> str:
    if not value.startswith(("http://", "https://")):
        return value
    parsed = urlsplit(value)
    directory = parsed.path.rsplit("/", 1)[0] + "/"
    file_name = parsed.path.rsplit("/", 1)[-1]
    base_url = urlunsplit((parsed.scheme, parsed.netloc, directory, "", ""))
    proxy_base = register_media_target(base_url, headers, kind="dash_media")
    return proxy_base + file_name + (f"?{parsed.query}" if parsed.query else "")


def rewrite_dash_manifest(data: bytes, base_url: str, headers: dict[str, str]) -> bytes | None:
    try:
        root = ET.fromstring(data)
    except ET.ParseError:
        return None

    def local_name(tag: str) -> str:
        return tag.rsplit("}", 1)[-1]

    if local_name(root.tag) != "MPD":
        return None
    namespace_match = re.match(r"\{([^}]+)\}", root.tag)
    namespace = namespace_match.group(1) if namespace_match else ""
    if namespace:
        ET.register_namespace("", namespace)
    upstream_root = _dash_directory_url(base_url)
    url_attributes = {"media", "initialization", "sourceURL", "index"}

    def walk(element: ET.Element, inherited_base: str) -> None:
        base_nodes = [child for child in element if local_name(child.tag) == "BaseURL"]
        child_base = inherited_base
        for index, node in enumerate(base_nodes):
            original = (node.text or "").strip()
            if not original:
                continue
            resolved = urljoin(inherited_base, original)
            node.text = register_media_target(resolved, headers, kind="dash_media")
            if index == 0:
                child_base = resolved
        for name, value in list(element.attrib.items()):
            if local_name(name) in url_attributes:
                element.set(name, _proxy_absolute_dash_value(value, headers))
        for child in element:
            if local_name(child.tag) != "BaseURL":
                walk(child, child_base)

    root_bases = [child for child in root if local_name(child.tag) == "BaseURL"]
    if root_bases:
        walk(root, base_url)
    else:
        base_tag = f"{{{namespace}}}BaseURL" if namespace else "BaseURL"
        base_element = ET.Element(base_tag)
        base_element.text = register_media_target(upstream_root, headers, kind="dash_media")
        insert_at = next(
            (index for index, child in enumerate(root) if local_name(child.tag) == "Period"),
            len(root),
        )
        root.insert(insert_at, base_element)
        for child in root:
            if child is not base_element:
                walk(child, upstream_root)

    return ET.tostring(root, encoding="utf-8", xml_declaration=True)


def rewrite_media_manifest(text: str, base_url: str, headers: dict[str, str]) -> str:
    def proxy_url(value: str, kind: str) -> str:
        target = urljoin(base_url, value)
        return (
            register_media_target(target, headers, kind=kind)
            if target.startswith(("http://", "https://"))
            else value
        )

    output = []
    next_uri_kind = "segment"
    for line in text.splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("#"):
            output.append(proxy_url(stripped, next_uri_kind))
            next_uri_kind = "segment"
            continue

        upper = stripped.upper()
        if upper.startswith("#EXT-X-STREAM-INF"):
            next_uri_kind = "manifest"
        if 'URI="' in line:
            if upper.startswith(("#EXT-X-KEY", "#EXT-X-SESSION-KEY")):
                uri_kind = "key"
            elif upper.startswith("#EXT-X-MAP"):
                uri_kind = "map"
            elif upper.startswith((
                "#EXT-X-MEDIA",
                "#EXT-X-I-FRAME-STREAM-INF",
                "#EXT-X-RENDITION-REPORT",
            )):
                uri_kind = "manifest"
            elif upper.startswith("#EXT-X-PRELOAD-HINT") and "TYPE=MAP" in upper:
                uri_kind = "map"
            else:
                uri_kind = "segment"
            line = re.sub(
                r'URI="([^"]+)"',
                lambda match: f'URI="{proxy_url(match.group(1), uri_kind)}"',
                line,
            )
        output.append(line)
    return "\n".join(output) + "\n"


def decode_media_manifest(data: bytes) -> str | None:
    """解码并规范化 HLS 文本，确保 #EXTM3U 是响应的第一个字符。"""
    try:
        if data.startswith((b"\xff\xfe", b"\xfe\xff")):
            text = data.decode("utf-16")
        else:
            text = data.decode("utf-8-sig")
    except UnicodeDecodeError:
        return None
    text = text.lstrip("\ufeff\x00 \t\r\n")
    return text if text.startswith("#EXTM3U") else None


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
        if parsed.path.startswith("/api/dash-media/"):
            self.api_dash_media(parsed)
            return
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

    def do_POST(self) -> None:
        if urlsplit(self.path).path == "/api/client-log":
            self.api_client_log()
            return
        self.send_json(404, {"error": "未知 API"})

    def end_headers(self) -> None:
        path = urlsplit(self.path).path
        if path in {"/", "/index.html", "/detail.html"}:
            self.send_header("Cache-Control", "no-store, max-age=0")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        super().end_headers()

    def api_client_log(self) -> None:
        try:
            length = int(self.headers.get("Content-Length") or "0")
        except ValueError:
            length = 0
        if length < 1 or length > 8192:
            self.send_json(413, {"error": "客户端日志大小无效"})
            return
        try:
            payload = json.loads(self.rfile.read(length).decode("utf-8", errors="replace"))
        except (TypeError, ValueError):
            self.send_json(400, {"error": "客户端日志不是有效 JSON"})
            return
        if not isinstance(payload, dict):
            self.send_json(400, {"error": "客户端日志格式错误"})
            return
        debug_id = re.sub(r"[^A-Za-z0-9_-]", "", str(payload.get("debugId") or ""))[:24] or "unknown"
        event = re.sub(r"[^A-Za-z0-9_.:-]", "", str(payload.get("event") or "event"))[:80]
        data = json.dumps(payload.get("data"), ensure_ascii=False, default=str)[:4000]
        data = data.replace("\r", "\\r").replace("\n", "\\n")
        print(f"[client:{debug_id}] {event} {data}", flush=True)
        self.send_response(204)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", "0")
        self.end_headers()

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

    def call_plugin(
        self,
        site: str,
        operation: str,
        data: dict[str, Any],
        cache_ttl: int = 0,
    ) -> Any:
        try:
            if cache_ttl > 0:
                return get_cached_plugin_result(site, operation, data, cache_ttl)
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
        result = self.call_plugin(site, "home", {}, cache_ttl=HOME_CACHE_TTL)
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
        result = self.call_plugin(
            site,
            "category",
            {"tid": tid, "page": page, "extend": {}},
            cache_ttl=CATEGORY_CACHE_TTL,
        )
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
            if player["mode"] == "media":
                if player["is_hls"]:
                    player["url"] = register_media_target(
                        player["url"], player["headers"], kind="manifest"
                    )
                    player["proxied"] = True
                elif player["is_dash"]:
                    player["url"] = register_media_target(
                        player["url"], player["headers"], kind="dash_manifest"
                    )
                    player["proxied"] = True
                elif player["headers"]:
                    player["url"] = register_media_target(
                        player["url"], player["headers"], kind="media"
                    )
                    player["proxied"] = True
            print("[player] " + json.dumps({
                "site": site,
                "flag": self.first(params, "flag"),
                "parse": bool(result.get("parse")) if isinstance(result, dict) else False,
                "jx": bool(result.get("jx")) if isinstance(result, dict) else False,
                "mode": player.get("mode"),
                "is_hls": player.get("is_hls"),
                "is_dash": player.get("is_dash"),
                "proxied": player.get("proxied", False),
                "source_url": str(player.get("source_url") or result.get("url") or "")[:500]
                    if isinstance(result, dict) else "",
                "output_url": str(player.get("url") or "")[:500],
            }, ensure_ascii=False), flush=True)
            self.send_json(200, player)
        except PluginError as exc:
            print("[player-error] " + json.dumps({
                "site": site,
                "flag": self.first(params, "flag"),
                "error": str(exc),
                "result": str(result)[:1000],
            }, ensure_ascii=False), flush=True)
            self.send_json(422, {"error": str(exc)})

    def api_dash_media(self, parsed: Any) -> None:
        remainder = parsed.path[len("/api/dash-media/"):]
        token, separator, encoded_path = remainder.partition("/")
        target = get_media_target(token)
        if not token or not separator or target is None or target[2] != "dash_media":
            self.send_json(404, {"error": "DASH 媒体代理地址已失效，请重新选择剧集"})
            return
        base_url, headers, _kind = target
        relative_path = unquote(encoded_path)
        if "\x00" in relative_path or relative_path.startswith(("/", "\\")):
            self.send_json(400, {"error": "DASH 媒体路径无效"})
            return
        upstream_url = base_url if not relative_path else urljoin(
            base_url if base_url.endswith("/") else base_url + "/",
            relative_path,
        )
        base_parts, upstream_parts = urlsplit(base_url), urlsplit(upstream_url)
        if (upstream_parts.scheme, upstream_parts.netloc) != (base_parts.scheme, base_parts.netloc):
            self.send_json(400, {"error": "DASH 媒体路径越界"})
            return
        query = parsed.query or upstream_parts.query or base_parts.query
        upstream_url = urlunsplit(upstream_parts._replace(query=query, fragment=""))
        request_headers = dict(headers)
        range_header = self.headers.get("Range")
        if range_header:
            request_headers["Range"] = range_header
        try:
            response = requests.get(
                upstream_url,
                headers=request_headers,
                timeout=30,
                verify=False,
                allow_redirects=True,
            )
        except requests.RequestException as exc:
            self.send_json(502, {"error": f"DASH 媒体请求失败：{exc}"})
            return

        body = response.content
        content_type = response.headers.get("Content-Type") or "application/octet-stream"
        if relative_path.lower().endswith(".webp") and len(body) >= 8:
            box_type = body[4:8]
            if box_type in {b"ftyp", b"styp", b"moof"} or b"moof" in body[:256]:
                content_type = "application/mp4"
        if response.status_code >= 400 or "init-stream" in relative_path:
            print("[dash-media] " + json.dumps({
                "token": token[:10],
                "path": relative_path[:300],
                "status": response.status_code,
                "range": bool(range_header),
                "content_type": content_type,
                "bytes": len(body),
                "prefix_hex": body[:32].hex(),
            }, ensure_ascii=False), flush=True)

        self.send_response(response.status_code)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        for name in ("Accept-Ranges", "Content-Range"):
            value = response.headers.get(name)
            if value:
                self.send_header(name, value)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def api_media_proxy(self, params: dict[str, list[str]]) -> None:
        token = self.first(params, "token")
        target = get_media_target(token)
        if target is None:
            self.send_json(404, {"error": "媒体代理地址已失效，请重新选择剧集"})
            return
        url, headers, kind = target
        request_headers = dict(headers)
        range_header = self.headers.get("Range")
        image_path = urlsplit(url).path.lower()
        image_wrapped_candidate = bool(re.search(r"\.(?:png|jpe?g|webp|gif)$", image_path))
        if kind in {"manifest", "dash_manifest"}:
            for name in list(request_headers):
                if name.lower() == "range":
                    request_headers.pop(name, None)
        elif range_header and not image_wrapped_candidate:
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
        upstream_status = status
        upstream_bytes = len(body)
        content_type = response.headers.get("Content-Type") or "application/octet-stream"
        transformed_kind = ""
        invalid_preview = ""

        final_image_path = urlsplit(response.url).path.lower()
        should_probe_full = status == 206 and bool(range_header) and (
            kind in {"segment", "map"}
            or content_type.lower().startswith("image/")
            or bool(re.search(r"\.(?:png|jpe?g|webp|gif)$", final_image_path))
        )
        if should_probe_full:
            try:
                full_response = requests.get(
                    url,
                    headers=dict(headers),
                    timeout=30,
                    verify=False,
                    allow_redirects=True,
                )
                full_body = full_response.content
                transport_stream = (
                    unwrap_png_transport_stream(full_body) if full_response.ok else None
                )
                if transport_stream is not None:
                    response = full_response
                    body = transport_stream
                    status = 200
                    content_type = "video/mp2t"
                    transformed_kind = "png-ts"
            except requests.RequestException:
                pass

        if not transformed_kind:
            if kind == "dash_manifest":
                dash_manifest = rewrite_dash_manifest(body, response.url, headers)
                if dash_manifest is not None:
                    body = dash_manifest
                    status = 200
                    content_type = "application/dash+xml; charset=utf-8"
                    transformed_kind = "dash-manifest"
                elif 200 <= status < 300:
                    invalid_preview = body[:160].decode("utf-8", errors="replace")
                    invalid_preview = re.sub(r"\s+", " ", invalid_preview).strip()[:160]
                    body = "上游返回了 HTTP 200，但内容不是有效的 DASH MPD".encode("utf-8")
                    status = 502
                    content_type = "text/plain; charset=utf-8"
                    transformed_kind = "invalid-dash-manifest"
            else:
                manifest_text = decode_media_manifest(body)
                if manifest_text is not None:
                    manifest = rewrite_media_manifest(manifest_text, response.url, headers)
                    body = manifest.encode("utf-8")
                    status = 200
                    content_type = "application/vnd.apple.mpegurl; charset=utf-8"
                    transformed_kind = "manifest"
                elif kind == "manifest" and 200 <= status < 300:
                    invalid_preview = body[:160].decode("utf-8", errors="replace")
                    invalid_preview = re.sub(r"\s+", " ", invalid_preview).strip()[:160]
                    body = "上游返回了 HTTP 200，但内容不是有效的 HLS 播放清单".encode("utf-8")
                    status = 502
                    content_type = "text/plain; charset=utf-8"
                    transformed_kind = "invalid-manifest"
                else:
                    transport_stream = unwrap_png_transport_stream(body)
                    if transport_stream is not None:
                        body = transport_stream
                        status = 200
                        content_type = "video/mp2t"
                        transformed_kind = "png-ts"

        content_type_lower = content_type.lower()
        looks_textual = (
            content_type_lower.startswith("text/")
            or any(value in content_type_lower for value in ("json", "xml", "javascript", "mpegurl"))
        )
        if transformed_kind or upstream_status >= 400 or kind in {"manifest", "dash_manifest"} or looks_textual:
            log_data = {
                "token": token[:10],
                "kind": kind,
                "upstream_status": upstream_status,
                "output_status": status,
                "range": bool(range_header),
                "content_type": content_type[:100],
                "upstream_bytes": upstream_bytes,
                "output_bytes": len(body),
                "prefix_hex": body[:48].hex(),
                "transformed": transformed_kind or "none",
            }
            if kind in {"manifest", "dash_manifest"} or transformed_kind in {
                "manifest", "invalid-manifest", "dash-manifest", "invalid-dash-manifest"
            } or looks_textual:
                body_preview = body[:1024].decode("utf-8", errors="replace")
                body_preview = re.sub(r"token=[A-Za-z0-9_-]+", "token=<redacted>", body_preview)
                log_data["body_prefix"] = body_preview
            if invalid_preview:
                log_data["upstream_preview"] = invalid_preview
            print("[media-proxy] " + json.dumps(log_data, ensure_ascii=False), flush=True)

        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        if not transformed_kind:
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
