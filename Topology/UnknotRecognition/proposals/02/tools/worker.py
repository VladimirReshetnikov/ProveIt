"""Isolated benchmark worker. Input is one JSON job on stdin; output is one JSON result."""
from __future__ import annotations

import gc
import json
from pathlib import Path
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
job = json.load(sys.stdin)
sys.path.insert(0, str(ROOT / "baseline" if job["engine"] == "baseline" else ROOT))
from fastunknot import Diagram, recognize
from fastunknot import scan
from fastunknot.simplify import simplify, descending_start

d = Diagram.from_json(job["diagram"])
method = job["method"]

def run():
    if method == "scan":
        order = job.get("order")
        return scan.khovanov_rank(d.pd, order=order, seconds=job["limit"],
                                  max_objects=job.get("max_objects", 500_000),
                                  check_d_squared=job.get("check_d_squared", False))
    if method == "pipeline":
        return recognize(d, seconds=job["limit"], max_objects=500_000).to_json()
    if method == "order":
        return {"order": scan.best_scan_order(d.pd, tries=12)}
    if method == "simplify":
        changed, trace = simplify(d)
        return {"remaining": changed.crossings, "moves": len(trace)}
    if method == "descending":
        return {"descending": descending_start(d) is not None}
    raise ValueError("unknown benchmark method")

samples = []
answer = None
status = "ok"
for _ in range(job.get("repeats", 3)):
    for name in ("circles", "glue", "_composition_plan", "_crossing_entries"):
        f = getattr(scan, name, None)
        if hasattr(f, "cache_clear"):
            f.cache_clear()
    gc.collect()
    start = time.perf_counter()
    try:
        answer = run()
    except (scan.ScanLimit, MemoryError) as exc:
        status = "limit"
        answer = {"reason": str(exc)}
    elapsed = time.perf_counter() - start
    samples.append(elapsed)
    if answer and answer.get("status") == "UNKNOWN":
        status = "limit"
    if status != "ok":
        break
result = {"status": status, "samples_seconds": samples,
          "median_seconds": statistics.median(samples), "answer": answer}
try:
    import resource
    # Linux: KiB; macOS: bytes. Not an allocation-only or per-run memory measure.
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    result["process_peak_rss_bytes"] = peak if sys.platform == "darwin" else 1024 * peak
except ImportError:
    pass
print(json.dumps(result))
