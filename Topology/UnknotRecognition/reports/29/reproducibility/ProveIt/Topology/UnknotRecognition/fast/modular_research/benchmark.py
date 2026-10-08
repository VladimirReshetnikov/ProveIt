"""Separate modular boundary arithmetic, raw scans, and full recognition.

Five shuffled paired rounds follow one excluded warmup per arm. Every call
constructs a fresh engine, and all arithmetic-stream samples include geometry
and terminal-response setup. The integer control invokes the identical baseline
implementation. Correctness comparisons and digests occur outside timed calls.

The synthetic workload appends a pure five-strand braid, preserving the closure
permutation while creating genuine interior vertices. Its queries are actual
matchings from the first nine stages of a production FastScan. These workloads
measure repeated suffix arithmetic, not difficulty of recognizing the knots.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
import signal
import statistics
import subprocess
import sys
from time import monotonic, perf_counter


HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from fastunknot import Diagram, recognize
from fastunknot.geometry import ScanLimit
from fastunknot.modular_shadow import ModularClosureShadow, modular_shadow_khovanov_decide
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import ClosureShadow, shadow_compressed_khovanov_decide
from determinant_research.boundary_tait import BoundaryTait as RationalBoundaryTait


WORD = [-2, 3, 2, 2, 4, 2, -3, -2, -1, 1, -2, -1, -2, -2]
ORDER = [5, 1, 10, 2, 9, 11, 13, 6, 7, 0, 12, 4, 8, 3]
PURE_TAIL = [1, 1, -2, -2, 3, 3, -4, -4]
CORPUS = ("conway", "kinoshita_terasaka", "conway_sum_2", "conway_sum_8",
          "hard_unknot_8", "grid_scrambled_unknot", "stress_braid5_36")
ARITHMETIC_ARMS = ("integer", "integer_control", "rational_boundary", "modular_boundary")
PIPELINE_ARMS = ("integer", "integer_control", "modular")
PRIME = 65521


class WallLimit(TimeoutError):
    pass


@contextmanager
def hard_limit(seconds):
    """Also bound the archived rational prototype, which has no callback."""
    def expired(signum, frame):
        raise WallLimit("benchmark hard wall-clock limit")
    previous = signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)


def digest(value):
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def source_hashes():
    files = list((HERE / "fastunknot").rglob("*.py"))
    files += [Path(__file__), HERE / "determinant_research/boundary_tait.py"]
    files += list((HERE.parent / "reports/26/detshadow").glob("*.py"))
    return {str(p.relative_to(HERE.parent)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(files)}


def summarize_pipeline(result):
    if isinstance(result, dict):
        data = result
    else:
        data = result.to_json()
    summary = {key: data[key] for key in ("status", "method", "stage", "crossings",
               "input_crossings", "reduced_crossings", "rank_capped", "rank_cap",
               "reduced_rank_lower_bound_capped", "shadow_exhausted", "euler_exhausted",
               "shadow_stats", "modular_observation", "stats") if key in data}
    if "order" in data:
        summary["order"] = data["order"]
        summary["order_sha256"] = digest(data["order"])
    evidence = data.get("evidence", {})
    if evidence:
        summary["evidence"] = evidence
    return summary


def stream_workload(tail_repetitions):
    word = WORD + PURE_TAIL * tail_repetitions
    diagram = Diagram.from_braid(5, word)
    order = ORDER + list(range(len(WORD), diagram.crossings))
    scan = FastScan(shape_cache=False)
    for crossing in order[:9]:
        scan.add_crossing(diagram.pd[crossing])
    pairs = [scan.algebra.pairs[m] for m in sorted(set(scan.mid) - {None})]
    data = dict(strands=5, word=word, pd=diagram.pd, order=order, stage=9,
                tail_repetitions=tail_repetitions, suffix_crossings=diagram.crossings - 9,
                frontier=len(scan.points), available_matching_count=len(pairs),
                source="actual FastScan matchings after nine crossings")
    data["pd_sha256"], data["order_sha256"] = digest(diagram.pd), digest(order)
    return diagram, order, pairs, data


def arithmetic_runner(diagram, order, pairs, seconds):
    def run(arm):
        if arm in ("integer", "integer_control"):
            engine = ClosureShadow(diagram.pd, order, max_states=None, max_work=None,
                                   deadline=monotonic() + seconds)
            vectors = tuple(engine.evaluate(9, pair) for pair in pairs)
            return dict(status="COMPLETE", vectors=vectors, stats=dict(engine.stats))
        if arm == "modular_boundary":
            engine = ModularClosureShadow(diagram.pd, order, primes=(PRIME,), max_states=None,
                                          max_work=None, deadline=monotonic() + seconds)
            vectors = tuple(engine.evaluate(9, pair) for pair in pairs)
            geometry = engine.boundary_geometry
            stats = dict(engine.stats)
            stats["interior_vertices"] = len(geometry.laplacian) - len(geometry.terminals)
            return dict(status="COMPLETE", vectors=vectors, stats=stats)
        engine = RationalBoundaryTait(diagram.pd, order, 9)
        vectors = []
        for pair in pairs:
            z, data = engine.evaluate(pair)
            parity = (data["zero_circles"] - 1) % 2
            if z[1 - parity] != 0:
                raise ArithmeticError("rational reference violated phase parity")
            a, difference = data["unreduced_euler"] // 2, z[parity]
            if (a + difference) % 2:
                raise ArithmeticError("rational reference produced a half-integer residue")
            vector = [0] * 4
            vector[parity], vector[parity + 2] = (a + difference) // 2, (a - difference) // 2
            vectors.append(tuple(vector))
        stats = dict(common_vertices=len(engine.laplacian), terminals=len(engine.terminals),
                     interior_vertices=len(engine.laplacian) - len(engine.terminals),
                     nullity=engine.kernel.nullity if engine.kernel else None,
                     kernel_builds=int(engine.kernel is not None),
                     distinct_determinants=len(engine.cache))
        return dict(status="COMPLETE", vectors=tuple(vectors), stats=stats)
    return run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "results/modular_benchmarks.json")
    parser.add_argument("--summary", type=Path)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--seconds", type=float, default=3.0)
    parser.add_argument("--seed", type=int, default=20261008)
    parser.add_argument("--scopes", nargs="+", choices=("streams", "raw", "pipeline", "disabled"),
                        default=("streams", "raw", "pipeline", "disabled"))
    args = parser.parse_args()
    rng = random.Random(args.seed)
    started = datetime.now(timezone.utc).isoformat()
    hashes_before = source_hashes()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=HERE, text=True).strip()
    rows, pilots = [], []
    verified_vectors, verified_statuses = 0, 0

    def invoke(run, arm):
        begin = perf_counter()
        try:
            with hard_limit(args.seconds + 0.15):
                value = run(arm)
        except (ScanLimit, MemoryError, WallLimit) as exc:
            return perf_counter() - begin, dict(status="UNKNOWN", censored=True,
                                                reason=type(exc).__name__ + ": " + str(exc))
        elapsed = perf_counter() - begin
        # All signatures and comparisons are deliberately outside timing.
        if "vectors" in value:
            vectors = tuple(tuple(int(c) % PRIME for c in v) for v in value.pop("vectors"))
            value["normalized_vectors"] = vectors
            value["vector_sha256"] = digest(vectors)
        value["censored"] = value.get("status") == "UNKNOWN"
        return elapsed, value

    def check_results(results, expected=None):
        nonlocal verified_vectors, verified_statuses
        for arm, (_, value) in results.items():
            if value["censored"]:
                continue
            signature = value.get("normalized_vectors", value["status"])
            if expected is None:
                expected = signature
            if signature != expected:
                raise AssertionError(("arm disagreement", arm, value, expected))
            if "normalized_vectors" in value:
                verified_vectors += len(signature)
            else:
                verified_statuses += 1
        return expected

    def compact(value):
        return {k: v for k, v in value.items() if k != "normalized_vectors"}

    def measure(name, scope, arms, run, data, warm=None):
        if warm is None:
            warm = {arm: invoke(run, arm) for arm in arms}
        expected = check_results(warm)
        row = dict(name=name, scope=scope, input=data, input_sha256=digest(data),
                   parameters=dict(seconds=args.seconds, max_objects=50000, prime=PRIME),
                   warmup_excluded={a: dict(seconds=t, result=compact(v))
                                    for a, (t, v) in warm.items()},
                   samples=[], repetitions=1)
        if any(v["censored"] for _, v in warm.values()):
            row.update(complete=False, censored_in_warmup=True, median_speedups=None,
                       note="No repeated timeout samples or speedup ratios are reported.")
            rows.append(row)
            print(scope, name, "censored during warmup", flush=True)
            checkpoint()
            return
        # Repeated fresh invocations stabilize sub-millisecond pipeline samples.
        repetitions = 1 if scope == "arithmetic-stream" else max(
            1, min(20, int(0.01 / max(t for t, _ in warm.values()))))
        row["repetitions"] = repetitions
        for round_index in range(args.rounds):
            shuffled = list(arms)
            rng.shuffle(shuffled)
            times, details, raw_times = {}, {}, {}
            for arm in shuffled:
                calls = [invoke(run, arm) for _ in range(repetitions)]
                expected = check_results({str(i): call for i, call in enumerate(calls)}, expected)
                raw_times[arm] = [t for t, _ in calls]
                times[arm] = statistics.mean(raw_times[arm])
                details[arm] = [compact(v) for _, v in calls]
            row["samples"].append(dict(round=round_index + 1, order=shuffled,
                                       seconds=times, call_seconds=raw_times, results=details))
        complete = all(not v["censored"] for sample in row["samples"]
                       for values in sample["results"].values() for v in values)
        row["complete"] = complete
        row["median_seconds"] = {a: statistics.median(s["seconds"][a] for s in row["samples"])
                                 for a in arms}
        row["median_speedups"] = ({a: statistics.median(
            s["seconds"][arms[0]] / s["seconds"][a] for s in row["samples"]) for a in arms[1:]}
            if complete else None)
        if scope == "arithmetic-stream" and complete:
            row["modular_over_rational_speedup"] = statistics.median(
                s["seconds"]["rational_boundary"] / s["seconds"]["modular_boundary"]
                for s in row["samples"])
        rows.append(row)
        print(scope, name, {a: round(v, 3) for a, v in (row["median_speedups"] or {}).items()}, flush=True)
        checkpoint()

    def checkpoint():
        hashes_after = source_hashes()
        changed = [p for p in sorted(set(hashes_before) | set(hashes_after))
                   if hashes_before.get(p) != hashes_after.get(p)]
        output = dict(description=__doc__, started_utc=started,
                      recorded_utc=datetime.now(timezone.utc).isoformat(),
                      revision=revision, python=platform.python_version(),
                      platform=platform.platform(), seed=args.seed, rounds=args.rounds,
                      cooperative_seconds=args.seconds, hard_seconds=args.seconds + 0.15,
                      warmup="One per arm excluded; shortened streams re-pilot afresh.",
                      control="integer_control calls the identical integer implementation.",
                      timing="Fresh constructors included; input matching-stream generation, correctness checks and digests excluded.",
                      caveat="Shared execution environment; ratios are paired medians, not asymptotic claims.",
                      verified_vectors=verified_vectors, verified_statuses=verified_statuses,
                      pilots=pilots, rows=rows, sources_before=hashes_before,
                      sources_after=hashes_after, changed_sources=changed)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2) + "\n")

    if "streams" in args.scopes:
        for k in (0, 1, 4, 12, 32):
            diagram, order, all_pairs, base_data = stream_workload(k)
            for count in (len(all_pairs), 50, 20):
                pairs = all_pairs[:count]
                run = arithmetic_runner(diagram, order, pairs, args.seconds)
                warm = {arm: invoke(run, arm) for arm in ARITHMETIC_ARMS}
                check_results(warm)
                if not any(v["censored"] for _, v in warm.values()):
                    break
                pilots.append(dict(name=f"pure_tail_{k}", matching_count=len(pairs),
                                   results={a: dict(seconds=t, result=compact(v))
                                            for a, (t, v) in warm.items()},
                                   note="Censored pilot excluded from paired estimates; shorter actual stream is tried."))
                checkpoint()
            data = dict(base_data, matching_count=len(pairs), pairs=pairs,
                        pairs_sha256=digest(pairs))
            measure(f"pure_tail_{k}", "arithmetic-stream", ARITHMETIC_ARMS, run, data, warm)

    for name in CORPUS:
        data = json.loads((HERE / "examples" / (name + ".json")).read_text())
        diagram = Diagram.from_json(data)
        reference_order = best_scan_order(diagram.pd, tries=min(len(diagram.pd), 12))
        input_data = dict(example=data, pd_sha256=digest(diagram.pd),
                          raw_order=reference_order, raw_order_sha256=digest(reference_order))
        for scope in args.scopes:
            if scope == "streams":
                continue
            def run(arm, scope=scope, data=data):
                fresh = Diagram.from_json(data)
                if scope == "raw":
                    decide = (modular_shadow_khovanov_decide if arm == "modular"
                              else shadow_compressed_khovanov_decide)
                    return summarize_pipeline(decide(fresh.pd, max_objects=50000, seconds=args.seconds))
                options = dict(backend="shadow-modular" if arm == "modular" else "shadow",
                               max_objects=50000, seconds=args.seconds)
                if scope == "disabled":
                    options.update(use_reduction=False, use_descending=False, use_seifert=False,
                                   use_braid=False, use_rational=False, use_braid_reduction=False,
                                   use_factorization=False, use_modular=False, use_jones=False,
                                   use_alexander=False, use_exact_alexander=False, use_r3=False)
                return summarize_pipeline(recognize(fresh, **options))
            label = {"raw": "raw-shadow", "pipeline": "recognition-default-filters",
                     "disabled": "recognition-disabled-filters"}[scope]
            measure(name, label, PIPELINE_ARMS, run, input_data)

    checkpoint()
    output = json.loads(args.output.read_text())
    lines = ["MODULAR CONTINUATION BENCHMARK", f"Revision: {revision}",
             f"Rounds: {args.rounds}; excluded warmups; seconds/call: {args.seconds}",
             "Fresh geometry/response setup included in arithmetic measurements.",
             f"Source changes during run: {output['changed_sources']}",
             f"Verified vector comparisons: {verified_vectors}; statuses: {verified_statuses}", ""]
    for row in rows:
        label = row["scope"] + " / " + row["name"]
        if not row["complete"]:
            lines.append(label + ": CENSORED; no speedup estimate")
            continue
        times = ", ".join(f"{a}={v:.6f}s" for a, v in row["median_seconds"].items())
        ratios = ", ".join(f"{a}={v:.3f}x" for a, v in row["median_speedups"].items())
        lines += [label, "  medians: " + times, "  integer/arm paired medians: " + ratios]
        if "modular_over_rational_speedup" in row:
            lines.append(f"  rational/modular: {row['modular_over_rational_speedup']:.3f}x")
    lines += ["", "Interpretation: arithmetic stream gains do not establish whole-recognizer gains.",
              "Normal filters may decide all corpus cases before either shadow observer runs.",
              "Disabled-filter and raw scopes deliberately expose the observer and must remain separate.",
              "Full raw samples, inputs, hashes, statistics and timeout pilots are in the JSON file."]
    text = "\n".join(lines) + "\n"
    if args.summary:
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(text)
    print(text, flush=True)


if __name__ == "__main__":
    main()
