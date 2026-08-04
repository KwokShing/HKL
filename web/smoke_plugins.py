# -*- coding: utf-8 -*-
from __future__ import annotations

import argparse
import json
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any

import server


def classify(error: str) -> str:
    value = error.casefold()
    if "modulenotfounderror" in value or "no module named" in value or "importerror" in value:
        return "missing_dependency"
    if "plugintimeout" in value or "调用超过" in value or "加载超时" in value:
        return "timeout"
    network_markers = (
        "connectionerror", "connecttimeout", "readtimeout", "sslerror", "name resolution",
        "remote disconnected", "connectionreseterror", "getaddrinfo failed",
    )
    if any(marker in value for marker in network_markers):
        return "upstream_network"
    if "timeout" in value or "超时" in value:
        return "upstream_network"
    return "code_compatibility"


def smoke(plugin: dict[str, Any]) -> dict[str, Any]:
    site_id = plugin["id"]
    runtime = server.PluginRuntime(server._safe_plugin_path(site_id), site_id, f"http://{server.HOST}:{server.PORT}")
    result = {"id": site_id, "name": plugin["name"], "missing": plugin["missing"], "status": "passed"}
    started = time.perf_counter()
    stage = "load"
    try:
        runtime._start()
        result["load_ms"] = round((time.perf_counter() - started) * 1000)
        stage = "home"
        home_started = time.perf_counter()
        normalized = server.normalize_home(runtime.call("home", {}))
        result["home_ms"] = round((time.perf_counter() - home_started) * 1000)
        result["categories"] = len(normalized["categories"])
        result["items"] = len(normalized["items"])
        if not normalized["categories"] and not normalized["items"]:
            result["status"] = "passed_empty"
    except Exception as exc:
        result["stage"] = stage
        result["error"] = f"{type(exc).__name__}: {exc}"
        result["status"] = classify(result["error"])
    finally:
        runtime.close()
    result["total_ms"] = round((time.perf_counter() - started) * 1000)
    return result

def main() -> int:
    parser = argparse.ArgumentParser(description="Smoke test every HKL Python Spider")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=25)
    parser.add_argument("--files", nargs="*")
    parser.add_argument("--output", type=Path, default=server.CACHE_DIR / "smoke-report.json")
    args = parser.parse_args()
    server.CALL_TIMEOUT = max(1, args.timeout)
    plugins = server.discover_plugins()
    if args.files:
        selected = set(args.files)
        plugins = [plugin for plugin in plugins if plugin["id"] in selected or plugin["name"] in selected]
    print(f"Testing {len(plugins)} plugins with {args.workers} workers, timeout={server.CALL_TIMEOUT}s", flush=True)
    results: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as executor:
        futures = {executor.submit(smoke, plugin): plugin for plugin in plugins}
        for completed, future in enumerate(as_completed(futures), 1):
            result = future.result()
            results.append(result)
            detail = f"categories={result.get('categories', '-')} items={result.get('items', '-')}"
            print(f"[{completed:03d}/{len(plugins):03d}] {result['status']:20} {result['id']} {detail}", flush=True)
    results.sort(key=lambda item: item["id"].casefold())
    counts = Counter(item["status"] for item in results)
    report = {"total": len(results), "timeout_seconds": server.CALL_TIMEOUT, "counts": dict(sorted(counts.items())), "results": results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Report: {args.output}")
    print("Summary: " + ", ".join(f"{key}={value}" for key, value in sorted(counts.items())))
    return 0 if all(item["status"].startswith("passed") for item in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())