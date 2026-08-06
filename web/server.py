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
from concurrent.futures import ThreadPoolExecutor, as_completed
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


BROWSER_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)
_BOT_USER_AGENT_RE = re.compile(r"^\s*(?:python-requests|python-urllib|urllib|httpx|aiohttp|curl|wget)", re.I)


class PluginError(RuntimeError):
    pass


_OPERATION_LABELS = {
    "home": "首页",
    "category": "该分类",
    "search": "搜索",
    "detail": "该影片",
    "player": "该片源",
}


def describe_plugin_error(message: str, operation: str = "") -> str:
    """把插件抛出的裸异常翻译成能看懂的说明。"""
    text = str(message).strip()
    label = _OPERATION_LABELS.get(operation, "该请求")
    if re.match(r"^(?:KeyError|IndexError):", text) or "has no attribute" in text:
        return f"{label}在插件里缺少必要状态或字段（{text}），站点接口可能已改版；换个分类或数据源试试"
    if re.match(r"^(?:JSONDecodeError|ValueError):", text) and "json" in text.lower():
        return f"{label}返回的不是合法 JSON（{text}），站点可能在拦截请求"
    return text


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


FEATURED_SOURCE_FILE = REPO_ROOT / "ok海豚665"
_FEATURED_LOCK = threading.Lock()
_FEATURED_SIGNATURE: tuple[int, int] | None = None
_FEATURED_ORDER: dict[str, int] = {}


def load_featured_sites() -> dict[str, int]:
    """读取 ok海豚665（TVBox 配置，内容是 JSON 但文件名没有扩展名）。

    取出 sites[].api 指向 py/ 脚本的条目，返回 {插件文件名: 配置里的次序}。
    按文件 mtime+size 缓存，页面加载时只会真正解析一次。
    """
    global _FEATURED_SIGNATURE, _FEATURED_ORDER

    try:
        stat = FEATURED_SOURCE_FILE.stat()
    except OSError:
        return {}
    signature = (stat.st_mtime_ns, stat.st_size)
    with _FEATURED_LOCK:
        if signature == _FEATURED_SIGNATURE:
            return _FEATURED_ORDER
        order: dict[str, int] = {}
        try:
            payload = json.loads(FEATURED_SOURCE_FILE.read_text(encoding="utf-8-sig"))
        except (OSError, ValueError) as exc:
            print(f"[featured] 解析 {FEATURED_SOURCE_FILE.name} 失败：{exc}", flush=True)
            payload = {}
        sites = payload.get("sites") if isinstance(payload, dict) else None
        for entry in sites or []:
            if not isinstance(entry, dict):
                continue
            api = str(entry.get("api") or "")
            file_name = unquote(api.rsplit("/", 1)[-1].split("?", 1)[0].split("#", 1)[0])
            # 只认指向 py 脚本的源，js/jar/csp_/接口地址一律跳过
            if not file_name.lower().endswith(".py") or "/" in file_name or "\\" in file_name:
                continue
            order.setdefault(file_name, len(order))
        _FEATURED_SIGNATURE = signature
        _FEATURED_ORDER = order
        print(f"[featured] {FEATURED_SOURCE_FILE.name}: {len(order)} 个 py 源", flush=True)
        return order


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

            def send(**overrides: Any) -> Any:
                return original_request(session, *args, **{**kwargs, **overrides})

            overrides: dict[str, Any] = {}
            try:
                try:
                    response = send()
                except requests.exceptions.SSLError as exc:
                    if kwargs.get("verify") is not None:
                        raise
                    # 证书链不完整的 CDN：仅本次请求降级校验，插件代码无需改动
                    print(f"[{site_id}] TLS 校验失败，改用免校验重试：{url[:160]}（{exc}）", flush=True)
                    overrides["verify"] = False
                    response = send(**overrides)
                if method == "GET" and response.status_code in {401, 403, 406, 412, 451}:
                    merged = {**dict(session.headers or {}), **(kwargs.get("headers") or {})}
                    agent = next(
                        (str(value) for name, value in merged.items() if str(name).lower() == "user-agent"),
                        "",
                    )
                    if _BOT_USER_AGENT_RE.match(agent):
                        overrides["headers"] = {
                            **(kwargs.get("headers") or {}),
                            "User-Agent": BROWSER_UA,
                        }
                        retried = send(**overrides)
                        if retried.status_code < 400:
                            print(
                                f"[{site_id}] {response.status_code} 拦截脚本 UA，改用浏览器 UA 成功：{url[:160]}",
                                flush=True,
                            )
                            response = retried
                return response
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

    home_invoked = False

    def dispatch(operation: str, data: dict[str, Any]) -> Any:
        nonlocal home_invoked
        if operation == "home":
            home_invoked = True
            return _invoke(instance, "homeContent", [(False,), ()])
        if operation == "category":
            return _invoke(instance, "categoryContent", [
                (data["tid"], str(data["page"]), False, data.get("extend", {})),
                (data["tid"], str(data["page"]), False),
                (data["tid"], str(data["page"])),
            ])
        if operation == "search":
            return _invoke(instance, "searchContent", [
                (data["keyword"], False, str(data["page"])),
                (data["keyword"], False),
                (data["keyword"],),
            ])
        if operation == "detail":
            return _invoke(instance, "detailContent", [([data["vod_id"]],), (data["vod_id"],)])
        if operation == "player":
            return _invoke(instance, "playerContent", [
                (data.get("flag", ""), data["vid"], []),
                (data.get("flag", ""), data["vid"], None),
                (data.get("flag", ""), data["vid"]),
                (data["vid"],),
            ])
        if operation == "local_proxy":
            # 多数插件按 dict 取参，少数按查询字符串处理，两种都试
            query = str(data.pop("__query__", ""))
            try:
                return _invoke(instance, "localProxy", [(data,)])
            except Exception:
                if not query:
                    raise
                return _invoke(instance, "localProxy", [(query,)])
        raise PluginError("未知插件操作")

    while True:
        try:
            message = connection.recv()
            operation = message.get("operation")
            data = message.get("data", {})
            if operation == "stop":
                break
            try:
                result = dispatch(operation, data)
            except (AttributeError, KeyError) as exc:
                # 有些插件把状态建在 homeContent 里（如优酷的 self.typeid），
                # 首页命中缓存或 worker 重启后直接翻分类就会缺状态，这里补跑一次首页再重试
                if home_invoked or operation not in {"category", "search", "detail", "player"}:
                    raise
                print(f"[{site_id}] {operation} 缺少首页状态（{type(exc).__name__}: {exc}），补跑 homeContent 后重试", flush=True)
                dispatch("home", {})
                result = dispatch(operation, data)
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
    # 有插件把片源名用 # 拼接（TVBox 规范是 $$$），数量能对上时按 # 还原
    if len(source_names) == 1 and len(source_values) > 1 and "#" in source_names[0]:
        hashed_names = [name for name in source_names[0].split("#") if name]
        if len(hashed_names) == len(source_values):
            source_names = hashed_names
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


def _first_param_value(params: dict[str, Any], key: str) -> str:
    value = params.get(key)
    if isinstance(value, (list, tuple)):
        return str(value[0]) if value else ""
    return str(value or "")


PAGE_RESOLVE_TIMEOUT = (10, 20)
PAGE_RESOLVE_MAX_BYTES = 3 * 1024 * 1024
PAGE_RESOLVE_MAX_DEPTH = 2
_PAGE_MEDIA_CACHE: dict[str, tuple[float, str]] = {}
_PAGE_MEDIA_CACHE_LOCK = threading.Lock()
PAGE_MEDIA_CACHE_TTL = 300
_MEDIA_IN_PAGE_RE = re.compile(
    r"https?://[^\s\"'<>\\]+?\.(?:m3u8|mp4|m4v|webm|flv|mkv|mpd)(?:\?[^\s\"'<>\\]*)?", re.I
)
_AD_URL_HINT_RE = re.compile(r"(?:^|[/_.-])(?:ads?|advert|guanggao|gg)(?:[/_.-]|\d|$)", re.I)


def _unescape_page_url(value: str) -> str:
    return unescape(str(value or "")).replace("\\/", "/").replace("\\u002F", "/").replace("\\u002f", "/")


def _decode_maccms_url(raw: str, encrypt: Any) -> str:
    value = _unescape_page_url(raw)
    if not value:
        return ""
    try:
        code = int(encrypt)
    except (TypeError, ValueError):
        code = 1 if "%" in value else 0
    if code == 2:
        import base64

        padded = value + "=" * (-len(value) % 4)
        try:
            value = base64.b64decode(padded).decode("utf-8", "replace")
        except Exception:
            return ""
    if code in (1, 2) or "%" in value:
        value = unquote(value)
    return value.strip()


def extract_maccms_player_url(page: str) -> str:
    """解析 MacCMS/苹果CMS 播放页里的 player_aaaa 配置（末尾可能没有分号）。"""
    for match in re.finditer(
        r"(?:var|let|const)\s+player_(?:aaaa|config|data)\s*=\s*(\{.*?\})\s*(?:;|</script>|\r?\n\s*(?:var|let|const)\s)",
        page,
        re.S,
    ):
        block = match.group(1)
        payload: Any = None
        try:
            payload = json.loads(block)
        except json.JSONDecodeError:
            pass
        if isinstance(payload, dict):
            url = _decode_maccms_url(payload.get("url"), payload.get("encrypt"))
        else:
            raw = re.search(r'"url"\s*:\s*"([^"]*)"', block)
            encrypt = re.search(r'"encrypt"\s*:\s*"?(\d+)"?', block)
            url = _decode_maccms_url(raw.group(1) if raw else "", encrypt.group(1) if encrypt else None)
        if url.startswith(("http://", "https://")):
            return url
    return ""


def _iframe_candidates(page: str, base_url: str) -> list[str]:
    found = []
    for src in re.findall(r"<iframe[^>]+src=[\"']([^\"']+)[\"']", page, re.I):
        candidate = _unescape_page_url(src)
        if not candidate or candidate.startswith(("javascript:", "about:", "data:")):
            continue
        absolute = urljoin(base_url, candidate)
        if not absolute.startswith(("http://", "https://")) or _AD_URL_HINT_RE.search(absolute):
            continue
        if absolute not in found:
            found.append(absolute)
    return found


def _fetch_page(url: str, headers: dict[str, Any]) -> str:
    request_headers = {
        "User-Agent": BROWSER_UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
    }
    for name, value in (headers or {}).items():
        text = str(value)
        if "\r" in text or "\n" in text:
            continue
        request_headers[str(name)] = text
    request_headers.setdefault("Referer", url)
    response = requests.get(
        url, headers=request_headers, timeout=PAGE_RESOLVE_TIMEOUT, verify=False, stream=True
    )
    response.raise_for_status()
    content_type = str(response.headers.get("Content-Type", "")).lower()
    if content_type and not any(
        token in content_type for token in ("text/", "html", "javascript", "json", "xml")
    ):
        response.close()
        return ""
    body = response.raw.read(PAGE_RESOLVE_MAX_BYTES, decode_content=True) or b""
    response.close()
    charset = ""
    match = re.search(r"charset=([\w-]+)", content_type)
    if match:
        charset = match.group(1)
    if not charset:
        meta = re.search(rb"charset=[\"']?([\w-]+)", body[:2048], re.I)
        charset = meta.group(1).decode("ascii", "ignore") if meta else "utf-8"
    try:
        return body.decode(charset, "replace")
    except LookupError:
        return body.decode("utf-8", "replace")


def resolve_page_media(url: str, headers: dict[str, Any], depth: int = 0) -> str:
    """把播放网页解析成可直接播放的媒体直链，失败返回空字符串。"""
    if depth >= PAGE_RESOLVE_MAX_DEPTH or not url.startswith(("http://", "https://")):
        return ""
    if depth == 0:
        with _PAGE_MEDIA_CACHE_LOCK:
            cached = _PAGE_MEDIA_CACHE.get(url)
            if cached and time.time() - cached[0] < PAGE_MEDIA_CACHE_TTL:
                return cached[1]
    try:
        page = _fetch_page(url, headers)
    except Exception as exc:
        print(f"[page-resolve] 抓取失败 {url[:200]} -> {exc}", flush=True)
        return ""
    if not page:
        return ""

    resolved = extract_maccms_player_url(page)
    if resolved and not is_direct_media_url(resolved):
        nested = resolve_page_media(resolved, {**(headers or {}), "Referer": url}, depth + 1)
        resolved = nested or ""
    if not resolved:
        for candidate in _MEDIA_IN_PAGE_RE.findall(page):
            candidate = _unescape_page_url(candidate)
            if _AD_URL_HINT_RE.search(urlsplit(candidate).path):
                continue
            resolved = candidate
            break
    if not resolved:
        for frame in _iframe_candidates(page, url):
            if is_direct_media_url(frame):
                resolved = frame
                break
            nested = resolve_page_media(frame, {**(headers or {}), "Referer": url}, depth + 1)
            if nested:
                resolved = nested
                break

    if resolved and depth == 0:
        with _PAGE_MEDIA_CACHE_LOCK:
            if len(_PAGE_MEDIA_CACHE) >= 512:
                _PAGE_MEDIA_CACHE.clear()
            _PAGE_MEDIA_CACHE[url] = (time.time(), resolved)
    if resolved:
        print(f"[page-resolve] {url[:160]} -> {resolved[:160]}", flush=True)
    return resolved


_MEDIA_KIND_CACHE: dict[str, tuple[float, str]] = {}
_MEDIA_KIND_CACHE_LOCK = threading.Lock()
MEDIA_KIND_CACHE_TTL = 300


def probe_media_kind(url: str, headers: dict[str, Any]) -> str:
    """地址看不出扩展名时，取开头一小段判断是 HLS 还是 DASH。"""
    if not url.startswith(("http://", "https://")):
        return ""
    with _MEDIA_KIND_CACHE_LOCK:
        cached = _MEDIA_KIND_CACHE.get(url)
        if cached and time.time() - cached[0] < MEDIA_KIND_CACHE_TTL:
            return cached[1]
    kind = ""
    try:
        request_headers = {"User-Agent": BROWSER_UA}
        for name, value in (headers or {}).items():
            text = str(value)
            if "\r" not in text and "\n" not in text:
                request_headers[str(name)] = text
        request_headers["Range"] = "bytes=0-2047"
        response = requests.get(url, headers=request_headers, timeout=(10, 20), verify=False, allow_redirects=True)
        if response.status_code in {200, 206}:
            content_type = str(response.headers.get("Content-Type", "")).lower()
            head = response.content[:2048].lstrip(b"\xef\xbb\xbf \t\r\n")
            if head.startswith(b"#EXTM3U") or "mpegurl" in content_type:
                kind = "hls"
            elif b"<MPD" in head or "dash+xml" in content_type:
                kind = "dash"
    except requests.RequestException:
        kind = ""
    with _MEDIA_KIND_CACHE_LOCK:
        if len(_MEDIA_KIND_CACHE) >= 1024:
            _MEDIA_KIND_CACHE.clear()
        _MEDIA_KIND_CACHE[url] = (time.time(), kind)
    if kind:
        print(f"[media-kind] {url[:160]} -> {kind}", flush=True)
    return kind


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
    source_url = ""
    media_kind = ""
    looks_like_web_page = bool(re.search(r"\.(?:html?|shtml|php|asp|aspx|jsp)(?:$|[?&#])", url, re.I))
    if not is_direct_media_url(url):
        # 地址不带媒体扩展名时先探测内容，很多站点用 play.php 之类直接吐 m3u8
        media_kind = probe_media_kind(url, headers)
    if not media_kind and not is_direct_media_url(url) and (requires_parse or looks_like_web_page):
        resolved = resolve_page_media(url, headers)
        if resolved:
            source_url = url
            headers = {**headers, "Referer": headers.get("Referer") or url}
            url = resolved
        elif requires_parse:
            raise PluginError("该片源返回的是平台网页，站内解析未找到直链；请选择其他片源")
    player = {
        "url": url,
        "mode": "media",
        "is_hls": is_hls_url(url) or media_kind == "hls",
        "is_dash": is_dash_url(url) or media_kind == "dash",
        "options": options,
        "headers": headers,
    }
    if source_url:
        player["source_url"] = source_url
        player["resolved_from_page"] = True
    return player


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


def _is_own_proxy_url(value: str) -> bool:
    """判断地址是否已经指向本机代理，避免二次代理。"""
    if value.startswith("/api/"):
        return True
    try:
        parts = urlsplit(value)
    except ValueError:
        return False
    return parts.hostname in {HOST, "localhost", "127.0.0.1"} and parts.path.startswith("/api/")


PTS_PROBE_BYTES = 48 * 1024
PTS_WRAP_SECONDS = (1 << 33) / 90000
DISCONTINUITY_PROBE_LIMIT = 12
PTS_CACHE_TTL = 600
SANITIZED_MANIFEST_CACHE_TTL = 300
_PTS_CACHE: dict[str, tuple[float, float | None]] = {}
_PTS_CACHE_LOCK = threading.Lock()
_SANITIZED_MANIFEST_CACHE: dict[str, tuple[float, str]] = {}
_SANITIZED_MANIFEST_CACHE_LOCK = threading.Lock()


def first_transport_stream_pts(data: bytes) -> float | None:
    """读取 MPEG-TS 里第一个视频/音频 PES 的 PTS（秒）。"""
    limit = len(data) - 188
    offset = data.find(b"\x47")
    if offset < 0:
        return None
    while 0 <= offset <= limit:
        if data[offset] != 0x47:
            offset = data.find(b"\x47", offset + 1)
            continue
        payload_start = bool(data[offset + 1] & 0x40)
        adaptation = (data[offset + 3] >> 4) & 0x3
        position = offset + 4
        if adaptation in (2, 3):
            position += 1 + data[offset + 4]
        if payload_start and position + 14 <= offset + 188 and data[position:position + 3] == b"\x00\x00\x01":
            stream_id = data[position + 3]
            if (0xE0 <= stream_id <= 0xEF or 0xC0 <= stream_id <= 0xDF) and data[position + 7] & 0x80:
                marker = data[position + 9:position + 14]
                pts = (
                    ((marker[0] >> 1) & 0x07) << 30
                    | marker[1] << 22
                    | ((marker[2] >> 1) & 0x7F) << 15
                    | marker[3] << 7
                    | (marker[4] >> 1)
                )
                return pts / 90000
        offset += 188
    return None


def probe_segment_pts(url: str, headers: dict[str, str]) -> float | None:
    """只下载分片开头一小段来取首个 PTS，用于核验时间轴是否真的断开。"""
    with _PTS_CACHE_LOCK:
        cached = _PTS_CACHE.get(url)
        if cached and time.time() - cached[0] < PTS_CACHE_TTL:
            return cached[1]
    pts: float | None = None
    try:
        response = requests.get(
            url,
            headers={**headers, "Range": f"bytes=0-{PTS_PROBE_BYTES - 1}"},
            timeout=(10, 20),
            verify=False,
            allow_redirects=True,
        )
        if response.status_code in {200, 206}:
            pts = first_transport_stream_pts(response.content)
    except requests.RequestException:
        pts = None
    with _PTS_CACHE_LOCK:
        if len(_PTS_CACHE) >= 4096:
            _PTS_CACHE.clear()
        _PTS_CACHE[url] = (time.time(), pts)
    return pts


def _split_hls_manifest(text: str) -> tuple[list[dict[str, Any]], list[str]]:
    """把清单拆成「标签 + 分片地址」序列，尾部标签单独返回；顺序完全保留。"""
    segments: list[dict[str, Any]] = []
    pending: list[str] = []
    for raw in text.replace("\r", "").split("\n"):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#"):
            pending.append(line)
            continue
        segments.append({"tags": pending, "uri": line})
        pending = []
    return segments, pending


def _segment_duration(tags: list[str]) -> float:
    for tag in tags:
        match = re.match(r"#EXTINF:\s*([\d.]+)", tag)
        if match:
            try:
                return float(match.group(1))
            except ValueError:
                return 0.0
    return 0.0


def _is_discontinuity_tag(tag: str) -> bool:
    return tag.startswith("#EXT-X-DISCONTINUITY") and not tag.startswith("#EXT-X-DISCONTINUITY-SEQUENCE")


def sanitize_hls_discontinuities(text: str, base_url: str, headers: dict[str, str]) -> str:
    """删除被证伪的 #EXT-X-DISCONTINUITY。

    有些站点会在时间轴其实连续的清单里插入 DISCONTINUITY，hls.js 会据此重设
    timestampOffset，拖动进度时就会出现 CHUNK_DEMUXER_ERROR_APPEND_FAILED
    （Parsed buffer not in DTS sequence）。这里只丢弃能证明多余的标记：
    首个分片之前的标记、重复标记，以及探测相邻分片 PTS 后确认时间轴连续的标记。
    """
    if not _is_discontinuity_tag_present(text) or "#EXT-X-MAP" in text:
        return text
    cache_key = hashlib.sha256(f"{base_url}\n{text}".encode("utf-8")).hexdigest()
    with _SANITIZED_MANIFEST_CACHE_LOCK:
        cached = _SANITIZED_MANIFEST_CACHE.get(cache_key)
        if cached and time.time() - cached[0] < SANITIZED_MANIFEST_CACHE_TTL:
            return cached[1]

    segments, tail = _split_hls_manifest(text)
    marked = [index for index, segment in enumerate(segments) if any(_is_discontinuity_tag(tag) for tag in segment["tags"])]
    if not segments or not marked:
        return text

    # 首片之前的 DISCONTINUITY 没有可对比的前序分片，VOD 清单里必然多余
    starts_at_zero = not re.search(r"#EXT-X-MEDIA-SEQUENCE:\s*([1-9]\d*)", text)
    drop = {0} if (marked and marked[0] == 0 and starts_at_zero) else set()

    candidates = [index for index in marked if index > 0][:DISCONTINUITY_PROBE_LIMIT]
    if candidates:
        wanted = sorted({index for candidate in candidates for index in (candidate - 1, candidate)})
        probes: dict[int, float | None] = {}
        with ThreadPoolExecutor(max_workers=min(6, len(wanted))) as pool:
            futures = {
                pool.submit(probe_segment_pts, urljoin(base_url, segments[index]["uri"]), headers): index
                for index in wanted
            }
            for future in as_completed(futures):
                probes[futures[future]] = future.result()
        for candidate in candidates:
            previous, current = probes.get(candidate - 1), probes.get(candidate)
            if previous is None or current is None:
                continue
            delta = current - previous
            if delta < -1:
                delta += PTS_WRAP_SECONDS
            expected = _segment_duration(segments[candidate - 1]["tags"])
            if expected <= 0:
                continue
            if abs(delta - expected) <= max(0.5, expected * 0.25):
                drop.add(candidate)

    output: list[str] = []
    removed = 0
    for index, segment in enumerate(segments):
        seen_discontinuity = False
        for tag in segment["tags"]:
            if _is_discontinuity_tag(tag):
                # 被证伪的标记直接删除，重复标记只保留一个
                if index in drop or seen_discontinuity:
                    removed += 1
                    continue
                seen_discontinuity = True
            output.append(tag)
        output.append(segment["uri"])
    output.extend(tail)
    result = "\n".join(output) + "\n" if removed else text
    if removed:
        print("[hls-sanitize] " + json.dumps({
            "url": base_url[:200],
            "segments": len(segments),
            "marked": len(marked),
            "removed": removed,
            "verified": sorted(drop),
        }, ensure_ascii=False), flush=True)
    with _SANITIZED_MANIFEST_CACHE_LOCK:
        if len(_SANITIZED_MANIFEST_CACHE) >= 256:
            _SANITIZED_MANIFEST_CACHE.clear()
        _SANITIZED_MANIFEST_CACHE[cache_key] = (time.time(), result)
    return result


def _is_discontinuity_tag_present(text: str) -> bool:
    return any(_is_discontinuity_tag(line.strip()) for line in text.splitlines() if line.startswith("#EXT-X-DIS"))


def _relative_own_proxy_url(value: str) -> str:
    """把本机绝对代理地址转成相对路径，避免端口不一致导致的跨源问题。"""
    if value.startswith("/"):
        return value
    parts = urlsplit(value)
    return urlunsplit(("", "", parts.path, parts.query, ""))


def rewrite_media_manifest(text: str, base_url: str, headers: dict[str, str]) -> str:
    def proxy_url(value: str, kind: str) -> str:
        if _is_own_proxy_url(value):
            return value
        target = urljoin(base_url, value)
        if _is_own_proxy_url(target):
            return target
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
            self.send_json(502, {"error": describe_plugin_error(str(exc), operation)})
        except (EOFError, BrokenPipeError, OSError) as exc:
            self.send_json(502, {"error": f"插件 worker 异常：{exc}"})
        return None

    def api_plugins(self, _params: dict[str, list[str]]) -> None:
        featured = load_featured_sites()
        plugins = [
            {**plugin, "featured_rank": featured.get(plugin["id"], -1)}
            for plugin in discover_plugins()
        ]
        self.send_json(200, {
            "plugins": plugins,
            "featured_source": FEATURED_SOURCE_FILE.name,
            "featured_total": sum(1 for plugin in plugins if plugin["featured_rank"] >= 0),
        })

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
            if player.get("resolved_from_page") and player["mode"] == "media":
                # 站内解析出直链后再交给插件一次，让它的代理/去广告逻辑仍然生效
                player = self.replay_player_with_direct_url(site, self.first(params, "flag"), player)
            if player["mode"] == "media" and _is_own_proxy_url(player["url"]):
                # 插件已经走本机 localProxy（例如 m3u8 去广告），不要再套一层媒体代理
                player["url"] = _relative_own_proxy_url(player["url"])
                player["proxied"] = True
            elif player["mode"] == "media":
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
                "resolved_from_page": player.get("resolved_from_page", False),
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

    def replay_player_with_direct_url(
        self, site: str, flag: str, player: dict[str, Any]
    ) -> dict[str, Any]:
        direct_url = player["url"]
        try:
            result = get_runtime(site).call("player", {"flag": flag, "vid": direct_url})
            replayed = normalize_player(result)
        except (PluginError, EOFError, BrokenPipeError, OSError) as exc:
            print(f"[player-replay] {site} 直链回喂失败，沿用站内解析结果：{exc}", flush=True)
            return player
        if replayed["mode"] != "media":
            return player
        if replayed["url"] != direct_url and not _is_own_proxy_url(replayed["url"]):
            # 插件换出了别的地址（可能又是网页），不予采纳
            return player
        replayed["source_url"] = player.get("source_url", "")
        replayed["resolved_from_page"] = True
        if not replayed.get("headers"):
            replayed["headers"] = player.get("headers", {})
        return replayed

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
                    manifest_text = sanitize_hls_discontinuities(manifest_text, response.url, headers)
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
        raw_query = "&".join(
            f"{quote(key, safe='')}={quote(value, safe='')}"
            for key, values in params.items()
            if key != "site"
            for value in values
        )
        target_url = unquote(_first_param_value(proxy_params, "url"))
        referer = unquote(_first_param_value(proxy_params, "referer"))
        upstream_headers = {"User-Agent": BROWSER_UA}
        if referer:
            upstream_headers["Referer"] = referer if referer.endswith("/") else referer + "/"

        status, content_type, body, failure = 502, "application/octet-stream", b"", ""
        try:
            result = get_runtime(site).call("local_proxy", {**proxy_params, "__query__": raw_query})
        except (PluginError, EOFError, BrokenPipeError, OSError) as exc:
            result, failure = None, f"localProxy 调用失败：{exc}"
        if result is not None:
            if not isinstance(result, (list, tuple)) or len(result) < 3:
                failure = "localProxy 返回格式错误"
            else:
                try:
                    status = int(result[0])
                except (TypeError, ValueError):
                    status = 200
                content_type = str(result[1] or "application/octet-stream")
                content = result[2]
                if isinstance(content, (bytes, bytearray)):
                    body = bytes(content)
                elif isinstance(content, list) and all(isinstance(item, int) for item in content):
                    body = bytes(content)
                else:
                    body = str(content or "").encode("utf-8")
                if not 200 <= status < 300:
                    failure = f"localProxy 返回 {status}"

        manifest_text = decode_media_manifest(body) if 200 <= status < 300 else None
        fallback = ""
        if manifest_text is None and is_hls_url(target_url):
            # 插件的清洗/下载失败时，服务端直接取原始清单，至少保证能播
            try:
                response = requests.get(
                    target_url, headers=upstream_headers, timeout=30, verify=False, allow_redirects=True
                )
                response.raise_for_status()
                manifest_text = decode_media_manifest(response.content)
                if manifest_text is not None:
                    target_url = response.url
                    fallback = failure or "localProxy 未返回播放清单"
                    status = 200
            except requests.RequestException as exc:
                failure = failure or f"原始清单抓取失败：{exc}"

        if manifest_text is not None:
            manifest_text = sanitize_hls_discontinuities(manifest_text, target_url, upstream_headers)
            body = rewrite_media_manifest(manifest_text, target_url, upstream_headers).encode("utf-8")
            content_type = "application/vnd.apple.mpegurl; charset=utf-8"
            print("[local-proxy] " + json.dumps({
                "site": site,
                "url": target_url[:200],
                "referer": upstream_headers.get("Referer", "")[:120],
                "output_bytes": len(body),
                "fallback": fallback,
            }, ensure_ascii=False), flush=True)
        elif failure and not body:
            print(f"[local-proxy-error] {site} {failure}", flush=True)
            self.send_json(502, {"error": failure})
            return
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
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
