"""Reproducible correctness checks and controlled factorization benchmarks.

Example (from the research artifact directory)::

    python tools/verify_factorization.py \
        --word-max 7 --planar-max 5 --random-diagrams 600 \
        --benchmark-max 512 --benchmark-repeats 3 --output results.json

Only Python's standard library and the upstream fastunknot package are used.
Input construction and certificate verification are outside timed regions.
Each timing uses a fresh Diagram instance, so cached traversal/face data from
the other method do not advantage either implementation.
"""
from __future__ import annotations

import argparse
from collections import Counter
import gc
import importlib
import sys
import types
import json
from pathlib import Path
import platform
import random
import statistics
import time

PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT / "fast"))

from fastunknot.diagram import Diagram, DiagramError

from fastunknot.interlace import (interlacement_components,
                              verify_interlacement_certificate,
                              visible_factors_interlacement)


_baseline_diagram = None
_baseline_factor = None


def configure_baseline(fast_root=None):
    """Load an archived fastunknot package under an isolated module name."""
    global _baseline_diagram, _baseline_factor
    fast_root = Path(fast_root) if fast_root else PACKAGE_ROOT / "baseline" / "fast"
    package_dir = fast_root.resolve() / "fastunknot"
    if not (package_dir / "factor.py").is_file():
        raise FileNotFoundError(f"baseline fastunknot/factor.py missing in {fast_root}")
    prefix = "_interlace_baseline"
    for name in list(sys.modules):
        if name == prefix or name.startswith(prefix + "."):
            del sys.modules[name]
    namespace = types.ModuleType(prefix)
    namespace.__path__ = [str(package_dir)]
    namespace.__package__ = prefix
    sys.modules[prefix] = namespace
    _baseline_diagram = importlib.import_module(prefix + ".diagram").Diagram
    _baseline_factor = importlib.import_module(prefix + ".factor").visible_factors


def baseline_factor(diagram):
    if _baseline_factor is None:
        configure_baseline()
    return _baseline_factor(_baseline_diagram(diagram.pd))


def structural_work(summands):
    """Exact internal recursive crossing visits on cyclic trefoil sums."""
    if type(summands) is not int or summands < 1:
        raise ValueError("summands must be a positive integer")
    return 3 * (summands * (summands + 1) // 2 - 1)


def cyclic_trefoil_sum(summands):
    """Deterministic quadratic-work benchmark generator."""
    if type(summands) is not int or summands < 1:
        raise ValueError("summands must be a positive integer")
    return cyclic_sum([Diagram.from_braid(2, [1, 1, 1])] * summands)


def canonical_words(n):
    """Every double-occurrence word, with labels ordered by first occurrence."""
    counts = [0] * n
    prefix = []

    def visit(opened):
        if len(prefix) == 2 * n:
            yield tuple(prefix)
            return
        for x in range(opened):
            if counts[x] == 1:
                counts[x] = 2
                prefix.append(x)
                yield from visit(opened)
                prefix.pop()
                counts[x] = 1
        if opened < n:
            counts[opened] = 1
            prefix.append(opened)
            yield from visit(opened + 1)
            prefix.pop()
            counts[opened] = 0

    yield from visit(0)


def brute_components(word):
    n = len(word) // 2
    places = [[] for _ in range(n)]
    for i, x in enumerate(word):
        places[x].append(i)
    adjacency = [set() for _ in range(n)]
    for x in range(n):
        a, b = places[x]
        for y in range(x):
            c, d = places[y]
            if a < c < b < d or c < a < d < b:
                adjacency[x].add(y)
                adjacency[y].add(x)
    unseen = set(range(n))
    groups = []
    while unseen:
        start = min(unseen)
        group, pending = set(), [start]
        while pending:
            x = pending.pop()
            if x in group:
                continue
            group.add(x)
            pending.extend(adjacency[x] - group)
        unseen.difference_update(group)
        groups.append(frozenset(group))
    return set(groups)


def word_diagram(word, mask):
    """A rotation choice for each crossing; rejects positive-genus maps."""
    n = len(word) // 2
    rows = [[-1] * 4 for _ in range(n)]
    seen = [False] * n
    for i, x in enumerate(word):
        slot = (3 if mask & (1 << x) else 1) if seen[x] else 0
        seen[x] = True
        rows[x][slot] = i
        rows[x][(slot + 2) % 4] = (i + 1) % (2 * n)
    return Diagram.from_pd(rows)


def pd_key(diagram):
    """Remove edge-label choices, retaining the upstream crossing row order."""
    labels = {}
    return tuple(tuple(labels.setdefault(e, len(labels)) for e in row)
                 for row in diagram.pd)


def check_diagram(diagram):
    old, cuts = baseline_factor(diagram)
    new, certificate = visible_factors_interlacement(diagram)
    fast, _ = visible_factors_interlacement(diagram, validate=False)
    assert Counter(map(pd_key, old)) == Counter(map(pd_key, new))
    assert [pd_key(x) for x in new] == [pd_key(x) for x in fast]
    assert sum(f.crossings for f in new) == diagram.crossings
    verify_interlacement_certificate([x // 4 for x in diagram.traversal()], certificate)
    assert len(cuts) == max(0, len(new) - 1)
    return len(new)


def cyclic_sum(diagrams):
    """Concatenate oriented Gauss words, keeping every crossing's rotation."""
    diagrams = [d for d in diagrams if d.crossings]
    n = sum(d.crossings for d in diagrams)
    if not n:
        return Diagram.from_pd([])
    rows = [[-1] * 4 for _ in range(n)]
    offset, position = 0, 0
    for d in diagrams:
        for dart in d.traversal():
            x, slot = divmod(dart, 4)
            rows[offset + x][slot] = position
            rows[offset + x][(slot + 2) % 4] = (position + 1) % (2 * n)
            position += 1
        offset += d.crossings
    return Diagram.from_pd(rows)


def exhaustive_words(maximum):
    report = []
    for n in range(maximum + 1):
        start, count = time.perf_counter(), 0
        for word in canonical_words(n):
            groups, forest = interlacement_components(word)
            assert set(map(frozenset, groups)) == brute_components(word)
            cert = {"crossing_components": groups, "interlacement_forest": forest}
            verify_interlacement_certificate(word, cert)
            count += 1
        row = {"crossings": n, "words": count,
               "seconds": time.perf_counter() - start}
        report.append(row)
        print("word checks", row, flush=True)
    return report


def exhaustive_planar(maximum):
    report = []
    for n in range(maximum + 1):
        start, candidates, spherical, split = time.perf_counter(), 0, 0, 0
        for word in canonical_words(n):
            for mask in range(1 << n):
                candidates += 1
                try:
                    d = word_diagram(word, mask)
                except DiagramError:
                    continue
                spherical += 1
                split += check_diagram(d) > 1
        row = {"crossings": n, "rotation_systems": candidates,
               "spherical": spherical, "decomposable": split,
               "seconds": time.perf_counter() - start}
        report.append(row)
        print("planar checks", row, flush=True)
    return report


def randomized_diagrams(count, seed, example_directory=None):
    rng = random.Random(seed)
    accepted, attempts, composed, examples = 0, 0, 0, 0
    while accepted < count:
        strands = rng.randrange(2, 9)
        length = rng.randrange(strands - 1, 81)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands) for _ in range(length)]
        attempts += 1
        try:
            d = Diagram.from_braid(strands, word)
        except DiagramError:
            continue
        if accepted % 4 == 0:
            d = cyclic_sum([d, Diagram.from_braid(2, [1, 1, 1])])
            composed += 1
        check_diagram(d)
        # Row/edge relabeling changes the algorithm's traversal starting point.
        rows = [list(row) for row in d.pd]
        rng.shuffle(rows)
        permutation = list(range(2 * d.crossings))
        rng.shuffle(permutation)
        check_diagram(Diagram.from_pd([[permutation[e] for e in row] for row in rows]))
        accepted += 1
    if example_directory:
        for path in sorted(Path(example_directory).glob("*.json")):
            check_diagram(Diagram.from_json(json.loads(path.read_text())))
            examples += 1
    row = {"seed": seed, "braids": accepted, "attempts": attempts,
           "cyclic_composites": composed, "relabelings": accepted,
           "upstream_examples": examples}
    print("random checks", row, flush=True)
    return row


def benchmark(maximum, repeats):
    base = Diagram.from_braid(2, [1, 1, 1])
    report = []
    k = 8
    while k <= maximum:
        d = cyclic_sum([base] * k)
        timings = {"baseline": [], "checked": [], "direct": []}
        processed = None
        for repeat in range(repeats):
            methods = ["baseline", "checked", "direct"]
            # Rotate order to reduce systematic cache/thermal/order effects.
            methods = methods[repeat % 3:] + methods[:repeat % 3]
            for method in methods:
                if _baseline_diagram is None:
                    configure_baseline()
                fresh = (_baseline_diagram if method == "baseline" else Diagram)(d.pd)
                gc.collect()
                start = time.perf_counter()
                if method == "baseline":
                    factors, evidence = _baseline_factor(fresh)
                else:
                    factors, evidence = visible_factors_interlacement(
                        fresh, validate=method == "checked")
                timings[method].append(time.perf_counter() - start)
                assert len(factors) == k and all(f.crossings == 3 for f in factors)
                if method == "baseline":
                    processed = sum(sum(cut["crossings"]) for cut in evidence)
                    assert processed == structural_work(k)
                else:
                    verify_interlacement_certificate(
                        [dart // 4 for dart in fresh.traversal()], evidence)
        medians = {method: statistics.median(times) for method, times in timings.items()}
        row = {"summands": k, "crossings": 3 * k,
               "baseline_recursive_crossings": processed,
               "repeats": repeats, "seconds": medians, "raw_seconds": timings,
               "checked_speedup": medians["baseline"] / medians["checked"]}
        report.append(row)
        print("benchmark", row, flush=True)
        k *= 2
    return report


def rejection_checks():
    word = (0, 1, 2, 0, 1, 2)
    invalid = [
        {"crossing_components": [[0], [1], [2]], "interlacement_forest": []},
        {"crossing_components": [[0, 1, 2]], "interlacement_forest": [[0, 1], [0, 1]]},
        {"crossing_components": [[0, 1], [1, 2]], "interlacement_forest": [[0, 1]]},
        {"crossing_components": [[0, 1]], "interlacement_forest": [[0, 1]]},
    ]
    for cert in invalid:
        try:
            verify_interlacement_certificate(word, cert)
        except ValueError:
            continue
        raise AssertionError("invalid certificate accepted")
    try:
        verify_interlacement_certificate((0, 0, 1, 1), {
            "crossing_components": [[0, 1]], "interlacement_forest": [[0, 1]]})
    except ValueError:
        pass
    else:
        raise AssertionError("nonalternating witness accepted")
    return len(invalid) + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--word-max", type=int, default=7)
    parser.add_argument("--planar-max", type=int, default=5)
    parser.add_argument("--random-diagrams", type=int, default=600)
    parser.add_argument("--seed", type=int, default=20261007)
    parser.add_argument("--examples", default=str(PACKAGE_ROOT / "baseline" / "fast" / "examples"))
    parser.add_argument("--baseline-fast-root", help="archived fast directory; defaults to packaged baseline/fast")
    parser.add_argument("--benchmark-max", type=int, default=0,
                        help="optional exploratory timing maximum; zero skips timings")
    parser.add_argument("--benchmark-repeats", type=int, default=3)
    parser.add_argument("--output", default="results.json")
    args = parser.parse_args()
    configure_baseline(args.baseline_fast_root)
    result = {
        "measurement_status": "Correctness validation; any optional timings are exploratory.",
        "python": platform.python_version(), "platform": platform.platform(),
        "implementation": platform.python_implementation(),
        "certificate_rejections": rejection_checks(),
        "exhaustive_words": exhaustive_words(args.word_max),
        "exhaustive_planar": exhaustive_planar(args.planar_max),
        "random_diagrams": randomized_diagrams(args.random_diagrams, args.seed, args.examples),
        "benchmarks": benchmark(args.benchmark_max, args.benchmark_repeats),
    }
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")
    print("All checks passed; saved", args.output, flush=True)


if __name__ == "__main__":
    main()
