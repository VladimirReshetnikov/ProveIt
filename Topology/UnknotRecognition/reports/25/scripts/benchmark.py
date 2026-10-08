#!/usr/bin/env python3
"""Paired mechanism benchmark, NOT a complete unknot-recognition benchmark.

Compares shared doubled-prefix preprocessing with a fair all-cut reference that
rebuilds prefix algebra per rotation, but generates/replays only the winning
certificate. Both use the same normal-form arithmetic and scalar DP. Imports,
input generation, and JSON output are outside timers. No timeouts censor results.
"""
from __future__ import annotations
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import argparse
from dataclasses import asdict
import json
import platform
import random
import statistics
import time
from cyclic_garside import compress, verify
from cyclic_garside.kernel import _prepare, _solve_cut, input_digest, length_lower_bound
from cyclic_garside.normalform import Counters, normal_form, validate
from cyclic_garside.oracles import old_barrier, geodesic_unknot, inverse_word


def naive_all_cuts(b, word):
    """Fair reference: no pruning, fresh algebra each cut, one final witness."""
    word = validate(b, word)
    n = len(word)
    counters = Counters()
    best, cut, plan, checks = n, 0, [], 0
    for s in range(n):
        rotated = word[s:] + word[:s]
        ids, queries, targets, count = _prepare(b, rotated, False, counters, None)
        value, candidate, work = _solve_cut(n, 0, ids, queries, targets, count, None)
        checks += work
        if value < best:
            best, cut, plan = value, s, candidate
    before_proof = counters.appends
    rotated = word[cut:] + word[:cut]
    records, output, end = [], [], 0
    for i, j, target in plan:
        output.extend(rotated[end:i])
        if target:
            output.append(target)
        _, proof = normal_form(b, rotated[i:j], trace=True, counters=counters)
        records.append(dict(start=i, end=j, target=target, proof=proof))
        end = j
    output.extend(rotated[end:])
    assert len(output) == best
    certificate = dict(schema="cyclic-garside-kernel-v1", strands=b,
                       input_digest=input_digest(b, word), mode="cyclic", rotation=cut,
                       output=output, replacements=records)
    stats = asdict(counters)
    stats.update(input_length=n, output_length=best, dp_target_checks=checks,
                 algebra_appends_before_proof=before_proof, rotations_evaluated=n)
    return dict(word=output, certificate=certificate, stats=stats)


def one_cycle(b, word):
    p = list(range(b))
    for a in word:
        i = abs(a) - 1
        p[i], p[i+1] = p[i+1], p[i]
    seen, i = set(), 0
    while i not in seen:
        seen.add(i)
        i = p[i]
    return len(seen) == b


def cases():
    rng = random.Random(202610071)
    while True:
        w = tuple(rng.choice((1,-1,2,-2,3,-3,4,-4)) for _ in range(22))
        if one_cycle(5, w):
            break
    m = 8
    u, v = (1,2,1)+(1,)*m, (2,1,2)+(1,)*m
    return [
        ("single_crossing", 2, (1,)),
        ("positive_4_braid", 4, (1,2,3)*3),
        ("ranktwo_barrier_h1", 4, old_barrier(1)),
        ("ranktwo_barrier_h4", 4, old_barrier(4)),
        ("geodesic_m12", 3, geodesic_unknot(12)),
        ("hidden_sleeve_m8", 3, u+(1,2)+inverse_word(v)),
        ("seeded_5_braid", 5, w),
    ]


def certified(arm, b, word):
    result = (naive_all_cuts(b, word) if arm == "naive" else
              compress(b, word, stop_at_lower_bound=False))
    assert verify(b, word, result["certificate"]) == tuple(result["word"])
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    rng = random.Random(202610072)
    raw, summary, inputs = [], [], []
    for name, b, word in cases():
        inputs.append(dict(name=name, strands=b, word=list(word)))
        expected = None
        for round_id in range(args.rounds):
            arms = ["naive", "shared_A", "shared_B"]
            rng.shuffle(arms)
            for arm in arms:
                start = time.perf_counter_ns()
                result = certified(arm, b, word)
                elapsed = (time.perf_counter_ns() - start) / 1e9
                current = (result["word"], result["certificate"])
                if expected is None:
                    expected = current
                assert current == expected
                raw.append(dict(case=name, round=round_id, arm=arm, seconds=elapsed,
                                stats=result["stats"]))
        samples = [x for x in raw if x["case"] == name]
        means = {a: statistics.median(x["seconds"] for x in samples if x["arm"] == a)
                 for a in ("naive", "shared_A", "shared_B")}
        paired, controls = [], []
        for r in range(args.rounds):
            values = {x["arm"]: x["seconds"] for x in samples if x["round"] == r}
            paired.append(values["naive"] / values["shared_A"])
            controls.append(values["shared_B"] / values["shared_A"])
        sa = next(x for x in samples if x["arm"] == "shared_A")
        nv = next(x for x in samples if x["arm"] == "naive")
        out = dict(case=name, n=len(word), strands=b, k=len(expected[0]),
                   shared_ms=means["shared_A"]*1000, naive_ms=means["naive"]*1000,
                   paired_speedup=statistics.median(paired),
                   aa_ratio=statistics.median(controls),
                   shared_appends=sa["stats"]["algebra_appends_before_proof"],
                   naive_appends=nv["stats"]["algebra_appends_before_proof"],
                   prefix_height=sa["stats"]["prefix_height"])
        summary.append(out)
        print(name, out, flush=True)
    default = []
    for h in (8, 32, 128):
        word = old_barrier(h)
        rows = []
        for r in range(args.rounds):
            start = time.perf_counter_ns()
            result = compress(4, word)
            assert verify(4, word, result["certificate"]) == tuple(result["word"])
            rows.append((time.perf_counter_ns()-start)/1e9)
        default.append(dict(h=h, n=len(word), seconds=rows, stats=result["stats"],
                            median_ms=statistics.median(rows)*1000,
                            certificate_bytes=len(json.dumps(result["certificate"],separators=(",",":")))))
    env = dict(python=sys.version, platform=platform.platform(), processor=platform.processor(),
               rounds=args.rounds, shuffle_seed=202610072, generation_seed=202610071,
               timer="time.perf_counter_ns", imports_timed=False, replay_timed=True,
               all_cut_pruning=False, full_recognizer=False)
    try:
        env["cpu_model"] = next(x.split(":",1)[1].strip() for x in Path("/proc/cpuinfo").read_text().splitlines()
                                if x.startswith("model name"))
    except (OSError, StopIteration):
        pass
    data = dict(environment=env, inputs=inputs, raw=raw, summary=summary, default_family=default)
    (ROOT/"data/benchmarks.json").write_text(json.dumps(data,indent=2)+"\n")
    lines = [r"\begin{tabular}{lrrrrrr}", r"\toprule",
             r"Input & $n$ & $k$ & Shared (ms) & Naive (ms) & Ratio & A/A \\",r"\midrule"]
    for row in summary:
        label = row["case"].replace("_",r"\_")
        lines.append(f'{label} & {row["n"]} & {row["k"]} & {row["shared_ms"]:.2f} & {row["naive_ms"]:.2f} & {row["paired_speedup"]:.2f} & {row["aa_ratio"]:.2f} '+r'\\')
    lines.extend([r"\bottomrule",r"\end{tabular}"])
    (ROOT/"docs/benchmark_table.tex").write_text("\n".join(lines)+"\n")
    lines = [r"\begin{tabular}{rrrrrr}",r"\toprule",r"$h$ & $n$ & $k$ & $R$ & Time (ms) & Certificate bytes \\",r"\midrule"]
    for row in default:
        s = row["stats"]
        lines.append(f'{row["h"]} & {row["n"]} & {s["output_length"]} & {s["prefix_height"]} & {row["median_ms"]:.2f} & {row["certificate_bytes"]} '+r'\\')
    lines.extend([r"\bottomrule",r"\end{tabular}"])
    (ROOT/"docs/default_table.tex").write_text("\n".join(lines)+"\n")

if __name__ == "__main__":
    main()
