# -*- coding: utf-8 -*-
"""供 HKL/py 插件本地运行的最小 TVBox Spider 兼容层。"""
from __future__ import annotations

import hashlib
import json
import os
import re
import threading
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit, urlunsplit

import requests

_CACHE_LOCK = threading.Lock()
_CACHE_ROOT = Path(os.environ.get("HKL_CACHE_DIR", Path(__file__).parents[1] / "web" / ".cache"))


def _normalize_url(url: str) -> str:
    if not isinstance(url, str):
        return url
    parsed = urlsplit(url)
    if not parsed.scheme or not parsed.netloc:
        return url
    path = re.sub(r"/{2,}", "/", parsed.path)
    return urlunsplit(parsed._replace(path=path))


class Spider:
    def __init__(self) -> None:
        self._session = requests.Session()

    def _get_session(self) -> requests.Session:
        """兼容未调用 super().__init__() 的旧版插件。"""
        session = getattr(self, "_session", None)
        if session is None:
            session = requests.Session()
            self._session = session
        return session

    def init(self, extend: Any = "") -> None:
        pass

    def fetch(self, url: str, **kwargs: Any) -> requests.Response:
        method = str(kwargs.pop("method", "GET")).upper()
        kwargs.setdefault("timeout", 20)
        return self._get_session().request(method, _normalize_url(url), **kwargs)

    def post(self, url: str, **kwargs: Any) -> requests.Response:
        kwargs.setdefault("timeout", 20)
        return self._get_session().post(_normalize_url(url), **kwargs)

    def getCache(self, key: str) -> Any:
        cache = self._read_cache()
        return cache.get(str(key))

    def setCache(self, key: str, value: Any) -> None:
        with _CACHE_LOCK:
            cache = self._read_cache()
            cache[str(key)] = value
            path = self._cache_path()
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")

    def getProxyUrl(self) -> str:
        return os.environ.get("HKL_PROXY_URL", "")

    def getName(self) -> str:
        return self.__class__.__name__

    def isVideoFormat(self, url: str) -> bool:
        return bool(re.search(r"\.(?:m3u8|mp4|flv|mkv|mpd)(?:$|[?#])", str(url), re.I))

    def manualVideoCheck(self) -> bool:
        return False

    def localProxy(self, _params: dict[str, Any]) -> list[Any]:
        return [404, "text/plain; charset=utf-8", "Not found"]

    def destroy(self) -> None:
        session = getattr(self, "_session", None)
        if session is not None:
            session.close()

    def log(self, value: Any) -> None:
        print(value, flush=True)

    def _cache_path(self) -> Path:
        module = self.__class__.__module__
        name = hashlib.sha256(module.encode("utf-8")).hexdigest()[:20]
        return _CACHE_ROOT / f"{name}.json"

    def _read_cache(self) -> dict[str, Any]:
        path = self._cache_path()
        if not path.is_file():
            return {}
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
            return value if isinstance(value, dict) else {}
        except (OSError, ValueError):
            return {}


# 兼容部分旧插件使用的基类名称。
BaseSpider = Spider