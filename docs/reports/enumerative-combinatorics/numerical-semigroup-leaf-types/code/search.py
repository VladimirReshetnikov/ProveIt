#!/usr/bin/env python3
"""Optional MILP discovery, not a proof dependency.

Example: python code/search.py --multiplicity 36 --frobenius 71 --seconds 15
Requires NumPy and SciPy. Any returned candidate is checked by verify.py using
exact integer arithmetic; a solver's numerical optimality status is not used in
any theorem. A time-limited run need not reproduce the historical candidate.
"""
from __future__ import annotations
import argparse
import json
import time
from typing import Any

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

from verify import inspect_tail


def search(m: int, F: int, seconds: float) -> dict[str, Any]:
    if m < 2 or F < 2 * m - 1 or seconds <= 0:
        raise ValueError('Require m >= 2, F >= 2*m-1, and seconds > 0.')
    rows: list[int] = []
    columns: list[int] = []
    values: list[float] = []
    lower: list[float] = []
    upper: list[float] = []

    def constraint(items: dict[int, int], lo: float = -np.inf,
                   hi: float = np.inf) -> None:
        row = len(upper)
        for column, value in items.items():
            rows.append(row)
            columns.append(column)
            values.append(value)
        lower.append(lo)
        upper.append(hi)

    def s(i: int) -> int:
        return i - 1

    def p(i: int) -> int:
        return F + i - 1

    variable_count = 2 * F
    for i in range(m, F + 1):
        for j in range(i, F - i + 1):
            terms = {s(i): 1, s(i + j): -1}
            terms[s(j)] = terms.get(s(j), 0) + 1
            constraint(terms, hi=1)
    for i in range(1, F + 1):
        constraint({p(i): 1, s(i): 1}, hi=1)
        for j in range(m, F - i + 1):
            constraint({p(i): 1, s(j): 1, s(i + j): -1}, hi=1)
    for n in range(F + 1, F + m + 1):
        coverage: dict[int, int] = {}
        for i in range(m, n // 2 + 1):
            j = n - i
            if j > F:
                continue
            z = variable_count
            variable_count += 1
            coverage[z] = 1
            constraint({z: 1, s(i): -1}, hi=0)
            if i != j:
                constraint({z: 1, s(j): -1}, hi=0)
        constraint(coverage, lo=1)

    matrix = coo_matrix((values, (rows, columns)),
                        shape=(len(upper), variable_count)).tocsc()
    objective = np.zeros(variable_count)
    objective[:F] = -1
    objective[F:2 * F] = -2
    lb, ub = np.zeros(variable_count), np.ones(variable_count)
    ub[:m - 1] = 0
    lb[m - 1] = 1
    ub[F - 1] = 0
    start = time.perf_counter()
    result = milp(
        objective,
        integrality=np.ones(variable_count),
        bounds=Bounds(lb, ub),
        constraints=LinearConstraint(matrix, lower, upper),
        options={'time_limit': seconds, 'mip_rel_gap': 0},
    )
    output: dict[str, Any] = {
        'm': m, 'F': F, 'status': int(result.status),
        'message': str(result.message),
        'seconds': round(time.perf_counter() - start, 3),
        'variables': variable_count, 'constraints': len(upper),
        'qualification': 'Solver status is numerical; only candidate validity is checked exactly.',
    }
    if result.x is not None:
        nongaps = [i for i in range(1, F + 1) if result.x[s(i)] > 0.5]
        try:
            certificate = inspect_tail(nongaps, F + 1)
            if certificate['m'] != m or not certificate['leaf']:
                raise AssertionError('Returned candidate is not a leaf of the requested multiplicity.')
            output['candidate'] = certificate
            output['exact_candidate_check'] = 'PASS'
            output['exact_objective_2t_minus_g'] = 2 * certificate['t'] - certificate['g']
        except AssertionError as error:
            output['exact_candidate_check'] = 'FAIL'
            output['candidate_error'] = str(error)
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--multiplicity', type=int, default=36)
    parser.add_argument('--frobenius', type=int, default=71)
    parser.add_argument('--seconds', type=float, default=15)
    args = parser.parse_args()
    try:
        result = search(args.multiplicity, args.frobenius, args.seconds)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
