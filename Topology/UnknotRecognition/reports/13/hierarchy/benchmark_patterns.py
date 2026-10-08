"""Reproduce full-input terminal-pattern benchmarks and exhaustive map counts."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import statistics
import sys
import time

from hierarchy import fixtures
from hierarchy.ball_patterns import classify_pattern, PatternError
from hierarchy.test_ball_patterns import baseline_classify


def measure(call, raw, repeats):
    times = []
    result = None
    for _ in range(repeats):
        start = time.perf_counter()
        result = call(raw)
        times.append(time.perf_counter() - start)
    return {"seconds": times, "median_seconds": statistics.median(times),
            "status": result["status"],
            "candidate_pairs": result.get("candidate_pairs"),
            "dual_triangles": result.get("dual_triangles"),
            "tested_edge_subsets": result.get("tested_edge_subsets")}


def small_map_census():
    counts = Counter()
    for vertices in (2, 4):
        for matching in fixtures.perfect_matchings(tuple(range(3 * vertices))):
            raw = fixtures.pattern_from_matching(vertices, matching)
            try:
                result = classify_pattern(raw)
            except PatternError:
                counts[f"{vertices}_vertices_non_spherical"] += 1
                continue
            status = result["status"]
            if status == "violating":
                status = result["witness"]["kind"]
            counts[f"{vertices}_vertices_{status}"] += 1
    return dict(sorted(counts.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("hierarchy/benchmark_results.json"))
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    rows = []
    for ring in (4, 8, 12, 16, 24, 32):
        raw = fixtures.bipyramid(ring)
        fast = measure(classify_pattern, raw, args.repeats)
        slow = measure(baseline_classify, raw, args.repeats)
        assert fast["status"] == slow["status"] == "essential"
        rows.append({"family": "bipyramid-dual", "ring_vertices": ring,
                     "pattern_vertices": 2 * ring, "pattern_edges": 3 * ring,
                     "darts": 6 * ring, "fast": fast, "report06": slow,
                     "median_speedup": slow["median_seconds"] / fast["median_seconds"]})
    scaling = []
    for ring in (64, 256, 1024, 4096, 16384):
        raw = fixtures.bipyramid(ring)
        scaling.append({"family": "bipyramid-dual", "ring_vertices": ring,
                        "darts": 6 * ring,
                        "fast": measure(classify_pattern, raw, args.repeats)})
    report = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version, "platform": platform.platform(),
        "repeats": args.repeats,
        "timing_boundary": (
            "Prepared raw JSON-like dict to returned full result. Both calls include "
            "validation, spherical-embedding checks, classification and result-data "
            "construction. Fixture generation and external JSON parsing/writing "
            "are excluded. The baseline wrapper constructs its unchecked dataclass "
            "then invokes the unmodified report-06 classifier, which validates once."
        ),
        "comparison": rows, "fast_scaling": scaling,
        "exhaustive_small_rotation_map_census": small_map_census(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in rows:
        print(f'{row["darts"]:5d} darts: fast '
              f'{row["fast"]["median_seconds"]:.6f}s, report06 '
              f'{row["report06"]["median_seconds"]:.6f}s, '
              f'{row["median_speedup"]:.1f}x')
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
