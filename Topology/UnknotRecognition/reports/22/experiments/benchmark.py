#!/usr/bin/env python3
"""Paired, capped measurements; UNKNOWN is never counted as a completed solve."""
from __future__ import annotations

import argparse
import json
import platform
import statistics
import sys
import time
from pathlib import Path

from corpus import ROOT, alexander_one_pretzel, conway_diagram, insert_pattern, rational_pair
from fastunknot.diagram import Diagram
from fastunknot.rational import montesinos_certificate, verify_montesinos_certificate
from fastunknot.recognize import recognize
from fastunknot.tangle_obstruction import recognize_with_subtangles


def median(values):
    return statistics.median(values)


def capture(result):
    return result.to_json()


def timed_recognition(spec, enabled, seconds, ceiling):
    # Fresh checked object, no warmed diagram caches; construction is outside
    # this timer and measured separately in the end-to-end column.
    diagram = Diagram.from_json(spec)
    start = time.perf_counter()
    result = recognize(diagram, use_rational=enabled, seconds=seconds, max_objects=ceiling)
    return time.perf_counter() - start, capture(result)


def recognition_case(name, spec, repeats, seconds, ceiling):
    (ROOT / "examples" / (name + ".json")).write_text(json.dumps(spec, indent=2) + "\n")
    timed_recognition(spec, False, seconds, ceiling)
    timed_recognition(spec, True, seconds, ceiling)
    rounds = []
    for _ in range(repeats):
        a1, result_a1 = timed_recognition(spec, False, seconds, ceiling)
        b_samples, result_b = [], None
        for _ in range(5):
            elapsed, result_b = timed_recognition(spec, True, seconds, ceiling)
            b_samples.append(elapsed)
        a2, result_a2 = timed_recognition(spec, False, seconds, ceiling)
        rounds.append({"baseline_before": a1, "new_samples": b_samples,
                       "baseline_after": a2, "baseline_before_result": result_a1,
                       "new_result": result_b, "baseline_after_result": result_a2})
    end_to_end = []
    for _ in range(repeats):
        start = time.perf_counter()
        d = Diagram.from_json(spec)
        result = recognize(d, seconds=seconds, max_objects=ceiling)
        end_to_end.append(time.perf_counter() - start)
    old_times = [(r["baseline_before"] + r["baseline_after"]) / 2 for r in rounds]
    new_times = [median(r["new_samples"]) for r in rounds]
    statuses = sorted({r[key]["status"] for r in rounds
                       for key in ("baseline_before_result", "baseline_after_result")})
    completed = "UNKNOWN" not in statuses
    if completed:
        assert all(r["baseline_before_result"]["status"] == r["new_result"]["status"]
                   == r["baseline_after_result"]["status"] for r in rounds)
    summary = {
        "name": name, "crossings": result.input_crossings,
        "baseline_statuses": statuses, "new_status": result.status,
        "baseline_method": rounds[0]["baseline_before_result"]["method"],
        "new_method": result.method,
        "median_baseline_seconds": median(old_times),
        "median_new_seconds": median(new_times),
        "median_new_end_to_end_seconds": median(end_to_end),
        "baseline_seconds_range": [min(old_times), max(old_times)],
        "new_seconds_range": [min(new_times), max(new_times)],
        "median_paired_speedup": median([a / b for a, b in zip(old_times, new_times)])
                                 if completed else None,
        "median_baseline_control_ratio": median([r["baseline_after"] / r["baseline_before"]
                                                   for r in rounds]),
        "completed_baseline": completed,
        "baseline_scan_stats": rounds[0]["baseline_before_result"].get("evidence", {})
                               .get("khovanov", {}).get("scan_stats"),
    }
    return {"summary": summary, "rounds": rounds, "new_end_to_end_seconds": end_to_end}


def local_case(name, diagram, patterns, repeats, seconds, ceiling):
    rounds = []
    for _ in range(repeats):
        values = []
        for mode in (False, True, False):
            d = Diagram.from_pd(diagram.pd)
            start = time.perf_counter()
            result = (recognize_with_subtangles(d, patterns=patterns, seconds=seconds,
                                                max_objects=ceiling) if mode
                      else recognize(d, seconds=seconds, max_objects=ceiling))
            values.append({"seconds": time.perf_counter() - start, "result": capture(result)})
        rounds.append(values)
    old = [(r[0]["seconds"] + r[2]["seconds"]) / 2 for r in rounds]
    new = [r[1]["seconds"] for r in rounds]
    completed = all(r[i]["result"]["status"] != "UNKNOWN" for r in rounds for i in (0, 2))
    if completed:
        assert all(r[0]["result"]["status"] == r[1]["result"]["status"]
                   == r[2]["result"]["status"] for r in rounds)
    return {"summary": {"name": name, "crossings": diagram.crossings,
                        "baseline_status": rounds[0][0]["result"]["status"],
                        "new_status": rounds[0][1]["result"]["status"],
                        "baseline_method": rounds[0][0]["result"]["method"],
                        "new_method": rounds[0][1]["result"]["method"],
                        "median_baseline_seconds": median(old), "median_new_seconds": median(new),
                        "median_paired_speedup": median([a / b for a, b in zip(old, new)])
                                                 if completed else None},
            "rounds": rounds}


def compressed_cases(repeats):
    cases = []
    for bits in (64, 256, 1024, 4096, 16384, 65536):
        a = (1 << bits) + 1
        spec = alexander_one_pretzel(a)["montesinos"]
        samples = []
        for _ in range(repeats):
            start = time.perf_counter()
            cert = montesinos_certificate(spec["e"], spec["tangles"])
            samples.append(time.perf_counter() - start)
        assert cert["status"] == "KNOTTED" and cert["determinant"] == 1
        assert verify_montesinos_certificate(spec["e"], spec["tangles"], cert)
        expanded = sum(abs(x) for cf in spec["tangles"] for x in cf)
        cases.append({"a_bit_length": a.bit_length(),
                      "expanded_crossing_bit_length": expanded.bit_length(),
                      "max_entry_bits": cert["max_entry_bits"],
                      "status": cert["status"], "determinant": 1,
                      "seconds": samples, "median_seconds": median(samples),
                      "pd_expanded": False})
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--seconds", type=float, default=3.0)
    parser.add_argument("--max-objects", type=int, default=20000)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("positive repeat count required")
    report = {"environment": {"python": sys.version, "platform": platform.platform(),
                              "processor": platform.processor()},
              "protocol": {"repeats": args.repeats, "seconds_cap": args.seconds,
                           "max_objects": args.max_objects,
                           "order": "baseline/new-five-samples/baseline; fresh PD caches",
                           "scope": "warm in-process; recognition excludes construction; end-to-end shown separately",
                           "unknown_policy": "censored baseline, no speedup computed"},
              "recognition": [], "local": [], "compressed": []}
    target = ROOT / "results" / "benchmarks.json"

    def save():
        target.write_text(json.dumps(report, indent=2) + "\n")

    sources = [(f"diagonal_m{m:02d}", rational_pair(("AB" * m)[:m]))
               for m in (2, 4, 6, 8, 10, 12)]
    sources += [("off_diagonal_m08", rational_pair("A" * 8, "B" * 8))]
    sources += [(f"alexander_one_a{a:02d}", alexander_one_pretzel(a)) for a in (3, 7, 31)]
    for name, spec in sources:
        entry = recognition_case(name, spec, args.repeats, args.seconds, args.max_objects)
        report["recognition"].append(entry)
        print(json.dumps(entry["summary"]), flush=True)
        save()
    for name in ("conway", "hard_unknot_8", "trefoil"):
        d = Diagram.from_json(json.loads((ROOT / "fast/examples" / f"{name}.json").read_text()))
        entry = local_case("catalogue_control_" + name, d, None,
                           args.repeats, args.seconds, args.max_objects)
        report["local"].append(entry); print(json.dumps(entry["summary"]), flush=True); save()
    for name, pattern in [
        ("planted_double_three", {"e": 0, "tangles": [[0, 3], [0, 3]]}),
        ("planted_alexander_one", {"e": 0, "tangles": [[0, -3], [0, 5], [0, 7]]}),
    ]:
        d, certificate = insert_pattern(conway_diagram(), pattern)
        (ROOT / "certificates" / (name + ".json")).write_text(json.dumps(certificate, indent=2) + "\n")
        (ROOT / "examples" / (name + ".json")).write_text(json.dumps({"pd": d.pd}, indent=2) + "\n")
        entry = local_case(name, d, [pattern], args.repeats, args.seconds, args.max_objects)
        report["local"].append(entry); print(json.dumps(entry["summary"]), flush=True); save()
    report["compressed"] = compressed_cases(args.repeats)
    save()
    print("Completed all benchmarks; raw data in results/benchmarks.json", flush=True)


if __name__ == "__main__":
    main()
