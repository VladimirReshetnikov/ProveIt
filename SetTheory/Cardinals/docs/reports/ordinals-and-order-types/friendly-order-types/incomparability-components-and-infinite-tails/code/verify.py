"""Reproduce the exhaustive finite checks. Run from this directory or by path."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import time

from friendly import FinitePoset, naturally_labeled_posets


def verify(max_n: int, grid_max: int) -> dict:
    results = []
    started = time.perf_counter()
    for n in range(max_n + 1):
        t = time.perf_counter()
        distribution = Counter()
        connected = 0
        for p in naturally_labeled_posets(n):
            exact = p.exact_rank()
            formula = p.graph_rank()
            witness = p.optimal_witness()
            if exact != formula or len(witness) != formula:
                raise AssertionError((p.up, exact, formula, witness))
            if not p.is_friendly(witness):
                raise AssertionError(("invalid witness", p.up, witness))
            if len(p.components()) == 1:
                connected += 1
                cuts = [x for x in p.maxima()
                        if len(p.components(p.full & ~(1 << x))) > 1]
                if len(cuts) > 1:
                    raise AssertionError(("two cut maxima", p.up, cuts))
            distribution[exact] += 1
        row = dict(n=n, posets=sum(distribution.values()),
                   connected=connected,
                   ranks={str(k): distribution[k] for k in sorted(distribution)},
                   seconds=round(time.perf_counter() - t, 6))
        results.append(row)
        print(json.dumps(row), flush=True)
    grids = []
    for m in range(2, grid_max + 1):
        for n in range(2, grid_max + 1):
            p = FinitePoset.chain(m).product(FinitePoset.chain(n))
            rank = p.exact_rank()
            if rank != m * n - 3 or p.graph_rank() != rank:
                raise AssertionError(("grid", m, n, rank))
            grids.append(dict(m=m, n=n, rank=rank, components=len(p.components())))
    return dict(
        description="Exact residual recursion versus the independent graph formula; "
                    "all witnesses checked; at most one cut maximum checked on connected posets.",
        finite_only=True,
        warning="These computations do not verify the transfinite theorems.",
        python=platform.python_version(),
        utc=datetime.now(timezone.utc).isoformat(),
        naturally_labeled=results,
        grid_checks=grids,
        total_posets=sum(row["posets"] for row in results),
        failures=0,
        seconds=round(time.perf_counter() - started, 6))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--grid-max", type=int, default=6)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    if not 0 <= args.max_n <= 8:
        parser.error("--max-n must lie between 0 and 8 (the search grows rapidly)")
    if not 2 <= args.grid_max <= 8:
        parser.error("--grid-max must lie between 2 and 8")
    result = verify(args.max_n, args.grid_max)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {result['total_posets']} posets; {len(result['grid_checks'])} grids.")


if __name__ == "__main__":
    main()
