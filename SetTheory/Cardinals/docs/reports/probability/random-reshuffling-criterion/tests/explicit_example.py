#!/usr/bin/env python3
"""Independent, standard-library-only exact check of the two-component example.

No imports from the main diagnostic or matrix-polynomial implementation are used.
This script enumerates all paths, proves equality to the stated rational values
at chosen steps, and records a reproducible CSV. The article proves the identities
and the full intervals; finite sampling alone does not do so.
"""
from __future__ import annotations
import csv
import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product, permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HESSIANS = (((3, 1), (1, 2)), ((1, 1), (1, 2)))
MEAN = ((F(2), F(1)), (F(1), F(2)))


def advance(x: tuple[F, F], h, eta: F) -> tuple[F, F]:
    return tuple(x[i] - eta * sum(F(h[i][j])*x[j] for j in range(2))
                 for i in range(2))


def score(x: tuple[F, F], objective: bool) -> F:
    if not objective:
        return sum(t*t for t in x)
    return sum(x[i]*MEAN[i][j]*x[j] for i in range(2) for j in range(2))/2


def expected(x: tuple[F, F], eta: F, replacement: bool, objective: bool) -> F:
    paths = list(product(range(2), repeat=2) if replacement else permutations(range(2)))
    total = F(0)
    for path in paths:
        y = x
        for i in path:
            y = advance(y, HESSIANS[i], eta)
        total += score(y, objective)
    return total/len(paths)


def decimal(x: F) -> Decimal:
    return Decimal(x.numerator)/Decimal(x.denominator)


def main() -> None:
    rows = []
    checks = 0
    for exponent in (2, 3, 4, 6, 8, 12, 20, 32, 40):
        eta = F(1, 2**exponent)
        x = (3*eta/4, F(1))
        wr = expected(x, eta, True, False)
        rr = expected(x, eta, False, False)
        gap = rr - wr
        target = F(9, 8)*eta**4*(2-9*eta**2)
        assert gap == target and gap > 0
        checks += 1
        fixed = (F(-1, 8), F(1))
        objective_gap = expected(fixed, eta, False, True)-expected(fixed, eta, True, True)
        assert objective_gap == eta**2*(120*eta**2-61*eta+4)/64
        checks += 1
        if exponent >= 4:
            assert objective_gap > 0
            checks += 1
        with localcontext() as ctx:
            ctx.prec = 100
            a = decimal(2*eta**2*(9*eta**2-8*eta+2))
            b = decimal(3*eta**3*(2*eta-1))
            # Rationalized negative eigenvalue: avoids subtracting close numbers.
            negative_eigenvalue = -2*b*b/(a+(a*a+4*b*b).sqrt())
            scaled = negative_eigenvalue/decimal(eta**4)
            rows.append({
                'eta': str(eta),
                'distance_WR': str(wr), 'distance_RR': str(rr),
                'distance_gap_RR_minus_WR': str(gap),
                'distance_gap_div_eta4': str(gap/eta**4),
                'objective_gap_fixed_state': str(objective_gap),
                'lambda_min_Delta_div_eta4_decimal': f'{scaled:.25f}',
            })
    (ROOT/'results').mkdir(exist_ok=True)
    with (ROOT/'results'/'explicit_gaps.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    result = {'status': 'PASS', 'exact_assertions': checks,
              'step_sizes': len(rows), 'arithmetic': 'fractions.Fraction',
              'eigenvalue_display': '100-digit Decimal, not used for exact assertions',
              'qualification': 'Independent enumeration; the article proves the all-step identities.'}
    (ROOT/'results'/'explicit_example.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
