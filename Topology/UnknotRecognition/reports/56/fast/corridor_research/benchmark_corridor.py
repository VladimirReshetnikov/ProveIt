"""Paired raw-scan and homogeneous two-term transfer measurements.

Each arm constructs a fresh scanner. Diagram construction and common crossing
order selection are excluded from actual-scan timings; scanning includes
quantum bookkeeping and all reduction work. Synthetic construction is excluded
from kernel timings. Verification is outside the timed region. The planted
complexes are valid homogeneous two-term complexes, not claimed knot stages.
"""
import argparse
import gc
import hashlib
import json
from math import ceil
from pathlib import Path
import sys
FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
import platform
import random
import statistics
from time import monotonic, perf_counter

from fastunknot import Diagram
from fastunknot.graded import GradedScan
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


def rank_binary(columns):
    pivots = {}
    for column in columns:
        while column:
            top = column.bit_length() - 1
            old = pivots.get(top)
            if old is None:
                pivots[top] = column
                break
            column ^= old
    return len(pivots)


def planted_two_term(scan_type, sources, sinks, core, dead=0, *, seed=2026100820,
                     options=None):
    """Nonzero three-dot transfer with adjustable dead branches and imbalance.

    All objects have a common matching on six boundary points. Survivor source
    objects have (h,q)=(0,0), survivor sinks have (1,6). Two scalar contractible
    layers at q=2,4 are joined by x0,x1,x2 radical maps. Extra contractible
    branches are reachable from sources but cannot reach a survivor sink.
    Hence pruning those branches preserves the transferred differential.
    """
    rng = random.Random(seed + sources * 1009 + sinks * 101 + core * 7 + dead)
    scan = scan_type(shape_cache=False, **(options or {}))
    matching = scan.algebra.intern(((0, 1), (2, 3), (4, 5)))
    scan.points = frozenset(range(6))
    degree, quantum, rows = [], [], []

    def vertices(number, h, q):
        first = len(rows)
        degree.extend([h] * number)
        quantum.extend([q] * number)
        rows.extend({} for _ in range(number))
        return list(range(first, first + number))

    source = vertices(sources, 0, 0)
    middle = [(vertices(core, 0, q), vertices(core, 1, q)) for q in (2, 4)]
    target = vertices(sinks, 1, 6)
    branches = [(vertices(dead, 0, q), vertices(dead, 1, q)) for q in (2, 4)]

    def invertible_block(a, b):
        binary = [1 << i for i in range(len(a))]
        if len(a) > 1:
            for _ in range(4 * len(a)):
                i, j = rng.sample(range(len(a)), 2)
                binary[i] ^= binary[j]
        for i, vertex in enumerate(a):
            rows[vertex].update({w: 1 for j, w in enumerate(b) if binary[i] >> j & 1})

    def radical_block(a, b, value):
        for vertex in a:
            for target_vertex in b:
                if rng.randrange(2):
                    rows[vertex][target_vertex] = value

    for a, b in middle + branches:
        invertible_block(a, b)
    radical_block(source, middle[0][1], 1 << 1)
    radical_block(middle[0][0], middle[1][1], 1 << 2)
    radical_block(middle[1][0], target, 1 << 4)
    if dead:
        radical_block(source, branches[0][1], 1 << 1)
        radical_block(branches[0][0], branches[1][1], 1 << 2)
    scan.mid = [matching] * len(rows)
    scan.deg, scan.qshift, scan.out = degree, quantum, rows
    scan.inc = [set() for _ in rows]
    for a, row in enumerate(rows):
        for b in row:
            scan.inc[b].add(a)
    scan.live = len(rows)
    return scan


def kernel_invariant(scan):
    """Invariant under homogeneous basis changes in this planted family."""
    source = [a for a, m in enumerate(scan.mid) if m is not None and scan.deg[a] == 0]
    target = [a for a, m in enumerate(scan.mid) if m is not None and scan.deg[a] == 1]
    index = {a: j for j, a in enumerate(target)}
    columns = []
    for a in source:
        value = 0
        for b, coefficient in scan.out[a].items():
            if coefficient != getattr(scan, "benchmark_top_monomial", 1 << 7):
                raise ArithmeticError("planted transfer has an unexpected monomial")
            value ^= 1 << index[b]
        columns.append(value)
    return dict(sources=len(source), sinks=len(target), coefficient_rank=rank_binary(columns))


def shared_suffix(scan_type, sources, branches, *, options=None):
    """Strict sparse family with R(1+2M) forward and R+2M reverse edge visits.

    For odd M the transferred map from every source is the nonzero monomial
    x0*x1*x2. All scalar pivots are identities. This controls for sparse input;
    ordinary Markowitz cancellation can itself be efficient on this family.
    """
    if branches % 2 != 1:
        raise ValueError("the nonzero shared-suffix fixture requires odd branches")
    scan = scan_type(shape_cache=False, **(options or {}))
    matching = scan.algebra.intern(((0, 1), (2, 3), (4, 5)))
    scan.points = frozenset(range(6))
    first_left, first_right = sources, sources + 1
    left = list(range(sources + 2, sources + 2 + branches))
    right = list(range(sources + 2 + branches, sources + 2 + 2 * branches))
    target = sources + 2 + 2 * branches
    total = target + 1
    scan.mid = [matching] * total
    scan.deg = [0] * sources + [0, 1] + [0] * branches + [1] * branches + [1]
    scan.qshift = [0] * sources + [2, 2] + [4] * (2 * branches) + [6]
    scan.out = [{first_right: 2} for _ in range(sources)] + [{} for _ in range(total - sources)]
    scan.out[first_left] = {first_right: 1, **{b: 4 for b in right}}
    for a, b in zip(left, right):
        scan.out[a] = {b: 1, target: 16}
    scan.inc = [set() for _ in range(total)]
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    scan.live = total
    return scan


def dead_leaves(scan_type, branches, *, options=None):
    """A nonzero x map plus M contractible radical branches with no sink."""
    scan = scan_type(shape_cache=False, **(options or {}))
    matching = scan.algebra.intern(((0, 1),))
    scan.points = frozenset((0, 1))
    left = list(range(1, 1 + branches))
    right = list(range(1 + branches, 1 + 2 * branches))
    target = 1 + 2 * branches
    total = target + 1
    scan.mid = [matching] * total
    scan.deg = [0] + [0] * branches + [1] * branches + [1]
    scan.qshift = [0] + [2] * (total - 1)
    scan.out = [{target: 2, **{b: 2 for b in right}}] + [{} for _ in range(total - 1)]
    for a, b in zip(left, right):
        scan.out[a][b] = 1
    scan.inc = [set() for _ in range(total)]
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    scan.live = total
    scan.benchmark_top_monomial = 2
    return scan


def make_kernel(family, scan_type, sources, sinks, core, dead, *, options=None):
    if family == "shared_suffix":
        return shared_suffix(scan_type, sources, core, options=options)
    if family == "dead_leaves":
        return dead_leaves(scan_type, dead, options=options)
    return planted_two_term(scan_type, sources, sinks, core, dead, options=options)


def state_digest(scan):
    state = dict(mid=scan.mid, deg=scan.deg, quantum=scan.qshift, out=scan.out)
    data = json.dumps(state, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def summary(samples, arms):
    result = {"seconds": {arm: statistics.median(s[arm] for s in samples) for arm in arms}}
    result["paired_ratios"] = {
        "standard_over_control": statistics.median(s["standard"] / s["control"] for s in samples),
        "prior_over_auto": statistics.median(s["prior"] / s["auto_pruned"] for s in samples),
        "standard_over_auto": statistics.median(s["standard"] / s["auto_pruned"] for s in samples),
        "standard_over_compressed": statistics.median(s["standard"] / s["compressed"] for s in samples),
        "prior_over_compressed": statistics.median(s["prior"] / s["compressed"] for s in samples),
        "auto_over_compressed": statistics.median(s["auto_pruned"] / s["compressed"] for s in samples),
        "ports_global_over_compressed": statistics.median(s["ports_global"] / s["compressed"] for s in samples),
        "standard_over_adaptive": statistics.median(s["standard"] / s["adaptive"] for s in samples),
        "full_over_pruned_forward": statistics.median(s["forward_full"] / s["forward_pruned"]
                                                       for s in samples),
        "pruned_forward_over_auto": statistics.median(s["forward_pruned"] / s["auto_pruned"]
                                                      for s in samples),
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--scope", choices=("all", "actual", "kernel"), default="all")
    parser.add_argument("--sample-seconds", type=float, default=0.015,
                        help="warm pilot target for each arm's repeated timing batch")
    parser.add_argument("--scan-seconds", type=float, default=30,
                        help="per-scanner cooperative resource limit")
    args = parser.parse_args()
    if args.rounds < 1 or args.sample_seconds <= 0 or args.scan_seconds <= 0:
        parser.error("round count and time limits must be positive")
    from fastunknot.corridor import CorridorScan, AdaptiveCorridorScan
    import fastunknot.graded_transfer as prior
    strategies = {
        "standard": (FastScan, {}),
        "control": (FastScan, {}),
        "graded_only": (GradedScan, {}),
        "prior": (prior.GradedTransferScan, {}),
        "forward_full": (CorridorScan, {"mode": "forward", "prune": False}),
        "forward_pruned": (CorridorScan, {"mode": "forward", "prune": True}),
        "backward_pruned": (CorridorScan, {"mode": "reverse", "prune": True}),
        "auto_pruned": (CorridorScan, {"mode": "auto", "prune": True}),
        "ports_global": (CorridorScan, {"direction_policy": "ports"}),
        "compressed": (CorridorScan, {"direction_policy": "ports", "scalar_engine": "components"}),
        "adaptive": (AdaptiveCorridorScan, {"mode": "auto", "prune": True}),
    }
    rng = random.Random(2026100821)
    result = dict(python=platform.python_version(), platform=platform.platform(),
                  seed=2026100821, rounds=args.rounds, timing_scope=__doc__,
                  batch_target_seconds=args.sample_seconds, batch_repetition_cap=32,
                  per_scanner_seconds=args.scan_seconds,
                  garbage_collection="gc.collect before each measured batch; collector remains enabled",
                  benchmark_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  implementation_sha256={name: hashlib.sha256((FAST /
                      "fastunknot" / name).read_bytes()).hexdigest()
                      for name in ("graded.py", "graded_transfer.py", "corridor.py", "scalar_components.py", "scan_fast.py", "planar.py")},
                  prior_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                  actual=[], kernels=[])
    if args.scope in ("all", "actual"):
        cases = [("two_strand_201", Diagram.from_braid(2, [1] * 201)),
                 ("torus_3_10", Diagram.from_braid(3, [1, 2] * 10)),
                 ("alternating_3_4", Diagram.from_braid(3, [1, -2] * 4)),
                 ("morton", Diagram.from_braid(4, [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]))]
        for name in ("conway", "hard_unknot_8"):
            path = FAST / "examples" / (name + ".json")
            cases.append((name, Diagram.from_json(json.loads(path.read_text()))))
        for name, diagram in cases:
            order = best_scan_order(diagram.pd)
            samples, metrics = [], {}
            expected = None
            repetitions = {}
            # Warm every implementation and choose a fixed per-arm repeat count.
            # Even tiny cases then contribute a batch long enough to time.
            for arm, (scan_type, options) in strategies.items():
                start = perf_counter()
                scan = scan_type(deadline=monotonic() + args.scan_seconds, **options)
                for crossing in order:
                    scan.add_crossing(diagram.pd[crossing])
                elapsed = perf_counter() - start
                repetitions[arm] = min(32, max(1, ceil(args.sample_seconds / elapsed)))
            repetitions["standard"] = repetitions["control"] = max(
                repetitions["standard"], repetitions["control"])
            for _ in range(args.rounds):
                arms = list(strategies)
                rng.shuffle(arms)
                sample = dict(order=arms)
                for arm in arms:
                    scan_type, options = strategies[arm]
                    gc.collect()
                    start = perf_counter()
                    for _ in range(repetitions[arm]):
                        scan = scan_type(deadline=monotonic() + args.scan_seconds, **options)
                        for crossing in order:
                            scan.add_crossing(diagram.pd[crossing])
                    elapsed = (perf_counter() - start) / repetitions[arm]
                    observed = scan.ranks_by_degree()
                    rank = scan.total_rank()
                    if expected is None:
                        expected = observed
                    if observed != expected:
                        raise ArithmeticError(f"actual homology disagreement: {name}, {arm}")
                    sample[arm] = elapsed
                    metrics[arm] = dict(rank=rank, by_degree=observed, stats=dict(scan.stats))
                samples.append(sample)
            row = dict(name=name, pd=diagram.pd, order=order, repetitions=repetitions,
                       samples=samples, metrics=metrics,
                       **summary(samples, strategies))
            result["actual"].append(row)
            print("actual", name, json.dumps(row["paired_ratios"]), flush=True)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + "\n")
    if args.scope in ("all", "kernel"):
        planted = [("dense", "source_heavy", 64, 1, 16, 0),
                   ("dense", "sink_heavy", 1, 64, 16, 0),
                   ("dense", "balanced", 16, 16, 16, 0),
                   ("dense", "dead_branches", 64, 1, 16, 64),
                   ("shared_suffix", "shared_suffix_15", 15, 1, 15, 0),
                   ("shared_suffix", "shared_suffix_63", 63, 1, 63, 0),
                   ("shared_suffix", "shared_suffix_255", 255, 1, 255, 0),
                   ("dead_leaves", "dead_leaves_255", 1, 1, 0, 255)]
        for family, name, sources, sinks, core, dead in planted:
            samples, metrics = [], {}
            expected = None
            exact = None
            repetitions = {}
            for arm, (scan_type, options) in strategies.items():
                scan = make_kernel(family, scan_type, sources, sinks, core, dead, options=options)
                scan.deadline = monotonic() + args.scan_seconds
                start = perf_counter()
                scan.eliminate()
                elapsed = perf_counter() - start
                repetitions[arm] = min(32, max(1, ceil(args.sample_seconds / elapsed)))
            repetitions["standard"] = repetitions["control"] = max(
                repetitions["standard"], repetitions["control"])
            for _ in range(args.rounds):
                arms = list(strategies)
                rng.shuffle(arms)
                sample = dict(order=arms)
                for arm in arms:
                    scan_type, options = strategies[arm]
                    batch = [make_kernel(family, scan_type, sources, sinks, core, dead,
                                         options=options) for _ in range(repetitions[arm])]
                    scan = batch[-1]
                    before = scan.live
                    scan.check_d_squared()
                    GradedScan.check_grading(scan)
                    gc.collect()
                    for prepared in batch:
                        prepared.deadline = monotonic() + args.scan_seconds
                    start = perf_counter()
                    for scan in batch:
                        scan.eliminate()
                    elapsed = (perf_counter() - start) / repetitions[arm]
                    observed = kernel_invariant(scan)
                    if observed["sources"] != sources or observed["sinks"] != sinks:
                        raise ArithmeticError("incorrect planted survivor count")
                    if expected is None:
                        expected = observed
                    if observed != expected:
                        raise ArithmeticError(f"kernel homology disagreement: {name}, {arm}")
                    if arm in ("prior", "forward_full", "forward_pruned", "backward_pruned", "auto_pruned", "ports_global", "compressed"):
                        digest = state_digest(scan)
                        if exact is None:
                            exact = digest
                        if digest != exact:
                            raise ArithmeticError(f"exact transfer disagreement: {name}, {arm}")
                    sample[arm] = elapsed
                    metrics[arm] = dict(invariant=observed, stats=dict(scan.stats))
                samples.append(sample)
            row = dict(name=name, family=family, sources=sources, sinks=sinks, core=core, dead=dead,
                       objects=before, repetitions=repetitions, samples=samples, metrics=metrics,
                       exact_transfer_sha256=exact, **summary(samples, strategies))
            result["kernels"].append(row)
            print("kernel", name, json.dumps(row["paired_ratios"]), flush=True)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + "\n")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
