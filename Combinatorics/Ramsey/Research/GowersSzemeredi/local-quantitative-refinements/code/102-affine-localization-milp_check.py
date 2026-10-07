#!/usr/bin/env python3
"""Optional floating-point exact-cover corroboration for C x C.

Requires numpy and scipy. The symbolic proofs in article.tex do not depend on
solver optimality/infeasibility reports. Every returned feasible partition is
checked exactly as a family of finite sets.

Run from the package root:
    python code/milp_check.py --orders 3 5 7 --output data/milp_results.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time

from verify import Field, all_zero_cells, check_partition, cross, zero_cycle

try:
    import numpy as np
    import scipy
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import csc_matrix
except ImportError as exc:
    raise SystemExit('Optional check requires numpy and scipy (with scipy.optimize.milp).') from exc


def run(q: int, seconds: float) -> dict:
    """Solve the minimum partition problem; test rigidity against both cycles."""
    F = Field(q)  # This optional solver accepts odd prime orders only.
    points = sorted(a+b for a in cross(F) for b in cross(F))
    index = {p: i for i, p in enumerate(points)}
    cells = all_zero_cells(F)
    n = len(cells)
    rows: list[int] = []
    cols: list[int] = []
    for j, cell in enumerate(cells):
        rows.extend(index[p] for p in cell)
        cols.extend([j]*len(cell))
    matrix = csc_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(points), n))
    constraints = [LinearConstraint(matrix, np.ones(len(points)), np.ones(len(points)))]

    def solve(cons: list, label: str) -> dict:
        start = time.monotonic()
        result = milp(np.ones(n), integrality=np.ones(n), bounds=Bounds(0, 1),
                      constraints=cons,
                      options={'time_limit': seconds, 'mip_rel_gap': 0.0})
        record = {'test': label, 'status': int(result.status),
                  'message': str(result.message), 'seconds': time.monotonic()-start}
        if result.x is not None:
            chosen = [cells[i] for i, value in enumerate(result.x) if value > .5]
            check_partition(chosen, points)
            record['exactly_checked_feasible_cells'] = len(chosen)
            record['cell_sizes'] = {str(size): sum(len(c)==size for c in chosen)
                                    for size in (1, q, q*q)}
            dual = getattr(result, 'mip_dual_bound', None)
            if dual is not None and np.isfinite(dual):
                record['floating_point_dual_bound'] = float(dual)
        return record

    records = [solve(constraints, 'minimum affine partition')]
    if q > 3:
        # Exclude the two exact known cycles by no-good cuts, and restrict cost.
        by_cell = {cell: i for i, cell in enumerate(cells)}
        restricted = list(constraints)
        restricted.append(LinearConstraint(np.ones(n), -np.inf, 4*q-3))
        for reverse in (False, True):
            cycle = zero_cycle(F, reverse)
            row = np.zeros(n)
            for cell in cycle:
                row[by_cell[cell]] = 1
            restricted.append(LinearConstraint(row, -np.inf, len(cycle)-1))
        records.append(solve(restricted, 'optimal cost with both cyclic partitions excluded'))
    return {'q': q, 'points': len(points), 'candidate_cells': n, 'runs': records}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7])
    parser.add_argument('--time-limit', type=float, default=30.0,
                        help='solver time limit in seconds per solve')
    parser.add_argument('--output', type=Path, default=Path('data/milp_results.json'))
    args = parser.parse_args()
    if args.time_limit <= 0:
        parser.error('--time-limit must be positive')
    results = []
    for q in args.orders:
        result = run(q, args.time_limit)
        results.append(result)
        print(json.dumps(result), flush=True)
    report = {'logical_status': 'Numerical solver corroboration, not formal or exact optimality certificates.',
              'numpy_version': np.__version__, 'scipy_version': scipy.__version__, 'results': results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')


if __name__ == '__main__':
    main()
