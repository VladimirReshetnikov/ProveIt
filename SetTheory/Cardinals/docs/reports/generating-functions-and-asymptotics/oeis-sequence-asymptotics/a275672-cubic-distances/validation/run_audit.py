#!/usr/bin/env python3
"""Reproduce the bounded independent search audit using only Python and C++17.

The default sources are the unmodified snapshots shipped with this directory.
Pass --v5, --top2, or --prefix to check other versions. Environment-variable
equivalents are A275672_AUDIT_V5, A275672_AUDIT_TOP2, A275672_AUDIT_PREFIX.
These checks supplement the written completeness proof; testing is not itself
an exhaustive proof for the large-grid computations.
"""

import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
BENCHMARKS = [(3, 4, 6), (4, 5, 19), (4, 6, 6), (5, 7, 27), (5, 8, 6)]
VARIANTS = [("v5", "diameters"), ("top2", "top2"),
            ("prefix", "top3"), ("prefix", "top4")]


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def run_logged(command, stem, timeout):
    result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    stem.with_suffix(".stdout").write_text(result.stdout, encoding="utf-8")
    stem.with_suffix(".stderr").write_text(result.stderr, encoding="utf-8")
    if result.returncode:
        raise RuntimeError(
            f"Command exited {result.returncode}: {shlex.join(map(str, command))}\n"
            f"See {stem.with_suffix('.stderr')}"
        )
    return result


def squared_distance(a, b):
    return sum((x - y) ** 2 for x, y in zip(a, b))


def independent_diameter_cases(n, target):
    """Explicit independent enumeration; deliberately no solver helper code."""
    points = list(itertools.product(range(n), repeat=3))
    palette = sorted({sum(x * x for x in p) for p in points} - {0})
    threshold = palette[target * (target - 1) // 2 - 1]
    permutations = list(itertools.permutations(range(3)))
    flips = list(itertools.product((False, True), repeat=3))
    representatives = set()
    for a, b in itertools.combinations(points, 2):
        if squared_distance(a, b) < threshold:
            continue
        images = []
        for permutation in permutations:
            for flip in flips:
                images.append(tuple(sorted(
                    tuple(n - 1 - p[permutation[i]] if flip[i]
                          else p[permutation[i]] for i in range(3))
                    for p in (a, b)
                )))
        representatives.add(min(images))
    return sorted(representatives)


def verify_witness(result, n, target, anchor):
    points = result["points"]
    assert len(points) == target
    assert all(len(p) == 3 and all(type(x) is int and 0 <= x < n for x in p)
               for p in points)
    points = [tuple(p) for p in points]
    assert len(set(points)) == target
    pairs = list(itertools.combinations(points, 2))
    distances = [squared_distance(a, b) for a, b in pairs]
    assert len(distances) == len(set(distances))
    longest = tuple(sorted(pairs[max(range(len(pairs)), key=distances.__getitem__)]))
    assert longest == anchor


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--v5", type=Path, default=os.environ.get("A275672_AUDIT_V5"))
    parser.add_argument("--top2", type=Path, default=os.environ.get("A275672_AUDIT_TOP2"))
    parser.add_argument("--prefix", type=Path, default=os.environ.get("A275672_AUDIT_PREFIX"))
    parser.add_argument("--cxx", default=os.environ.get("A275672_AUDIT_CXX", "g++"),
                        help="C++ compiler command, optionally including flags")
    parser.add_argument("--output", type=Path, default=Path("audit_output"))
    parser.add_argument("--compile-timeout", type=float, default=60)
    parser.add_argument("--case-timeout", type=float, default=45)
    parser.add_argument("--solver-seconds", type=float, default=40)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Run without Python -O: verification assertions must be enabled.")

    manifest = json.loads((HERE / "source_manifest.json").read_text(encoding="utf-8"))
    sources = {
        profile: (getattr(args, profile) or HERE / manifest[profile]["path"]).resolve()
        for profile in ("v5", "top2", "prefix")
    }
    for source in sources.values():
        if not source.is_file():
            parser.error(f"Source file not found: {source}")
    output = args.output.resolve()
    logs = output / "raw_logs"
    logs.mkdir(parents=True, exist_ok=True)
    compiler = shlex.split(args.cxx)
    if not compiler:
        parser.error("Compiler command is empty.")

    original_records = json.loads(
        (HERE / "recorded" / "diameter_prefix_results.json").read_text(encoding="utf-8")
    )
    expected_status = {
        (r["n"], r["target"], r["case"], r["variant"], r["mode"]): r["status"]
        for r in original_records
    }
    hashes = {profile: hashlib.sha256(path.read_bytes()).hexdigest()
              for profile, path in sources.items()}
    write_json(output / "source_hashes.json", hashes)
    random_results = {}
    case_results = []
    group_summaries = []
    suffix = ".exe" if os.name == "nt" else ""

    with tempfile.TemporaryDirectory(prefix="a275672-audit-") as temporary:
        build = Path(temporary)
        binaries = {}
        for profile, source in sources.items():
            directory = build / profile
            directory.mkdir()
            solver_copy = directory / "solver_under_audit.cpp"
            shutil.copyfile(source, solver_copy)
            harness_copy = directory / "random_reference_harness.cpp"
            shutil.copyfile(HERE / "random_reference_harness.cpp", harness_copy)
            harness_binary = directory / ("random_audit" + suffix)
            solver_binary = directory / ("solver" + suffix)
            run_logged(compiler + ["-O2", "-std=c++17", str(harness_copy),
                                   "-o", str(harness_binary)],
                       logs / f"compile_random_{profile}", args.compile_timeout)
            run_logged(compiler + ["-O2", "-std=c++17", str(solver_copy),
                                   "-o", str(solver_binary)],
                       logs / f"compile_solver_{profile}", args.compile_timeout)
            binaries[profile] = solver_binary
            result = run_logged([str(harness_binary)], logs / f"random_{profile}",
                                args.case_timeout)
            data = json.loads(result.stdout)
            assert data["status"] == "MATCH" and data["random_induced_instances"] == 500
            assert data["sat"] + data["unsat"] == 500
            random_results[profile] = data
            print(json.dumps({"profile": profile, **data}), flush=True)
        write_json(output / "random_search_results.json", random_results)

        for n, target, expected_count in BENCHMARKS:
            anchors = independent_diameter_cases(n, target)
            assert len(anchors) == expected_count
            group = []
            for case, anchor in enumerate(anchors):
                baseline = None
                for profile, mode in VARIANTS:
                    command = [str(binaries[profile]), str(n), str(target),
                               str(args.solver_seconds), mode, str(case)]
                    stem = logs / f"n{n}_k{target}_case{case}_{profile}_{mode}"
                    process = run_logged(command, stem, args.case_timeout)
                    result = json.loads(process.stdout)
                    assert result["status"] in ("SAT", "UNSAT"), result
                    if baseline is None:
                        baseline = result["status"]
                    assert result["status"] == baseline
                    key = (n, target, case, profile, mode)
                    assert result["status"] == expected_status[key], key
                    if result["status"] == "SAT":
                        verify_witness(result, n, target, anchor)
                    record = {"n": n, "target": target, "case": case,
                              "variant": profile, "mode": mode,
                              "status": result["status"], "nodes": result["nodes"]}
                    case_results.append(record)
                    group.append(record)
            summary = {"n": n, "target": target, "diameter_cases": expected_count,
                       "program_runs": len(group),
                       "sat_cases": sum(r["variant"] == "v5" and r["status"] == "SAT"
                                        for r in group),
                       "status": "ALL_VARIANTS_MATCH"}
            group_summaries.append(summary)
            print(json.dumps(summary), flush=True)
    assert len(case_results) == 256
    write_json(output / "diameter_prefix_results.json", case_results)
    write_json(output / "diameter_prefix_summary.json", group_summaries)
    print(f"Verified 1500 reference comparisons and 256 CLI cases; results: {output}")


if __name__ == "__main__":
    main()
