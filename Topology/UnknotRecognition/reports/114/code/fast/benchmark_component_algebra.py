"""Paired production scans and isolated dense/sparse composition kernels.

Scans include order selection and fresh scanner construction, but no earlier
recognition filters or input loading. Kernel timings include a cold first
composition; interning the matching is outside the timing boundary. Every
comparison asserts exact equality, with a separate standard/standard control.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, khovanov_rank
from fastunknot.component_algebra import accelerated_planar_class
from fastunknot.planar import Planar


def paired(function, rounds, rng):
    samples = []
    for _ in range(rounds):
        arms = ["standard", "control", "component", "component-dense"]
        rng.shuffle(arms)
        sample = {"order": arms}
        answers = {}
        for arm in arms:
            answer, elapsed = function("standard" if arm == "control" else arm)
            answers[arm] = answer
            sample[arm] = elapsed
        assert all(answer == answers["standard"] for answer in answers.values())
        samples.append(sample)
    return dict(samples=samples, median_aa=statistics.median(s["standard"]/s["control"] for s in samples),
                median_speedup={arm: statistics.median(s["standard"]/s[arm] for s in samples)
                                for arm in ("component", "component-dense")})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    rng = random.Random(2026100716)
    scans = []
    for name in ("conway", "kinoshita_terasaka", "conway_sum_2", "hard_unknot_8", "torus_3_5",
                 "unknot_braid40"):
        diagram = Diagram.from_json(json.loads((here/"examples"/(name+".json")).read_text()))
        metrics = {}

        def scan(mode):
            started = perf_counter()
            result = khovanov_rank(diagram.pd, composition=mode)
            elapsed = perf_counter() - started
            metrics[mode] = result.get("composition_stats", {})
            return result["by_degree"], elapsed

        result = dict(name=name, **paired(scan, args.rounds, rng), metrics=metrics)
        scans.append(result)
        print(name, result["median_speedup"], result["median_aa"], metrics, flush=True)
    cls = accelerated_planar_class(Planar)
    kernels = []
    for kind in ("dense", "near_equal", "sparse"):
        for arcs in (6, 8, 10):
            matching = tuple((2*i, 2*i+1) for i in range(arcs))
            if kind == "sparse":
                f = sum(1 << s for s in rng.sample(range(1 << arcs), 3))
                g = sum(1 << s for s in rng.sample(range(1 << arcs), 3))
            else:
                f = rng.getrandbits(1 << arcs)
                g = f ^ (1 << rng.randrange(1 << arcs)) if kind == "near_equal" else rng.getrandbits(1 << arcs)
            assert f and g and f != g

            def kernel(mode):
                if mode == "standard":
                    alg = Planar(shape_cache=False)
                else:
                    alg = cls(shape_cache=False, minimum_pairs=0 if mode == "component-dense" else 64,
                              method="fast" if mode == "component-dense" else "auto")
                a = alg.intern(matching)
                started = perf_counter()
                answer = alg.compose(a, a, a, f, g)
                return answer, perf_counter() - started

            result = dict(kind=kind, arcs=arcs, left_hex=hex(f), right_hex=hex(g),
                          monomial_pairs=f.bit_count()*g.bit_count(),
                          **paired(kernel, args.rounds, rng))
            kernels.append(result)
            print(kind, arcs, result["median_speedup"], result["median_aa"], flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100716,
        rounds=args.rounds, timing_scope=__doc__, scans=scans, kernels=kernels), indent=2) + "\n")


if __name__ == "__main__":
    main()
