"""Fresh raw homology runs; preparation excluded, order selection included.

Seven paired shuffled trials compare the ordinary scanner, a second identical
control, eager residue prediction, and adaptive cancellation. Every
homological degree must agree. This measures no earlier recognition filters.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, khovanov_rank
from fastunknot.residue import AdaptiveScan, ResidueScan
from fastunknot.scan_fast import FastScan


def dense_two_term(scan_type, size):
    """Synthetic valid complex with a full-rank residue and one survivor.

    No claim is made that this density occurs in a supplied knot scan.
    Preparation is deterministic and excluded from the kernel timings.
    """
    rng = random.Random(2026100723 + size)
    binary = [1 << i for i in range(size)]
    for _ in range(8 * size):
        a, b = rng.sample(range(size), 2)
        binary[a] ^= binary[b]
    binary.append(rng.getrandbits(size))
    scan = scan_type(shape_cache=False)
    matching = scan.algebra.intern(((0, 1), (2, 3), (4, 5)))
    total = 2 * size + 1
    scan.points = frozenset(range(6))
    scan.mid = [matching] * total
    scan.deg = [0] * (size + 1) + [1] * size
    scan.out = [({size + 1 + j: 2 * rng.randrange(1, 128) + ((binary[i] >> j) & 1)
                  for j in range(size)} if i <= size else {}) for i in range(total)]
    scan.inc = [set() if i <= size else set(range(size + 1)) for i in range(total)]
    scan.live = total
    return scan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(2026100722)
    cases = [("two_strand_201", Diagram.from_braid(2, [1]*201)),
             ("torus_3_10", Diagram.from_braid(3, [1, 2]*10)),
             ("alternating_3_4", Diagram.from_braid(3, [1, -2]*4)),
             ("morton", Diagram.from_braid(4, [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]))]
    for name in ("conway", "hard_unknot_8"):
        path = Path(__file__).parent / "examples" / (name + ".json")
        cases.append((name, Diagram.from_json(json.loads(path.read_text()))))
    rows = []
    for name, diagram in cases:
        expected = khovanov_rank(diagram.pd, seconds=30)
        assert khovanov_rank(diagram.pd, reduction="residue", seconds=30)["by_degree"] == expected["by_degree"]
        samples, metrics = [], {}
        for _ in range(args.rounds):
            arms = ["standard", "control", "residue", "adaptive"]
            rng.shuffle(arms)
            sample = {"order": arms}
            for arm in arms:
                start = perf_counter()
                result = khovanov_rank(diagram.pd, seconds=30,
                                       reduction=arm if arm in ("residue", "adaptive") else "standard")
                sample[arm] = perf_counter() - start
                assert result["by_degree"] == expected["by_degree"]
                metrics[arm] = result
            samples.append(sample)
        row = dict(name=name, pd=diagram.pd, samples=samples, standard=metrics["standard"],
                   residue=metrics["residue"], adaptive=metrics["adaptive"],
                   median_speedup=statistics.median(s["standard"]/s["residue"] for s in samples),
                   median_adaptive_speedup=statistics.median(s["standard"]/s["adaptive"] for s in samples),
                   median_aa=statistics.median(s["standard"]/s["control"] for s in samples))
        rows.append(row)
        print(name, round(row["median_speedup"], 3), round(row["median_aa"], 3),
              round(row["median_adaptive_speedup"], 3), metrics["adaptive"]["stats"], flush=True)
    kernels = []
    for size in (16, 32, 64):
        samples, metrics = [], {}
        for _ in range(args.rounds):
            arms = ["standard", "control", "residue", "adaptive"]
            rng.shuffle(arms)
            sample = {"order": arms}
            for arm in arms:
                scan_type = {"residue": ResidueScan, "adaptive": AdaptiveScan}.get(arm, FastScan)
                scan = dense_two_term(scan_type, size)
                scan.check_d_squared()
                start = perf_counter()
                scan.eliminate()
                sample[arm] = perf_counter() - start
                assert scan.live == 1 and scan.ranks_by_degree() == {0: 1} and not any(scan.out)
                metrics[arm] = dict(scan.stats)
            samples.append(sample)
        row = dict(size=size, samples=samples, stats=metrics,
                   median_speedup=statistics.median(s["standard"]/s["residue"] for s in samples),
                   median_adaptive_speedup=statistics.median(s["standard"]/s["adaptive"] for s in samples),
                   median_aa=statistics.median(s["standard"]/s["control"] for s in samples))
        kernels.append(row)
        print("synthetic_two_term", size, row["median_speedup"], row["median_adaptive_speedup"],
              row["median_aa"], flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100722,
        rounds=args.rounds, timing_scope=__doc__, cases=rows,
        kernel_scope=dense_two_term.__doc__, kernels=kernels), indent=2) + "\n")


if __name__ == "__main__":
    main()
