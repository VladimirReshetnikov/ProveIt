#!/usr/bin/env python3
"""Exact certificate for the first four depths of OEIS A290268.

Python standard library only. No floating-point arithmetic is used.
The analytic infinite-to-finite reduction is proved in article.tex.
This program verifies its finite obligations, not the analytic lemmas.

Run: python3 code/verify.py
Regenerate CSV/JSON: python3 code/verify.py --write-data
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from collections import Counter, defaultdict
from pathlib import Path

PARAMETERS = {3: (14, 38), 4: (85, 185)}
MODULI = (1009, 1013)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def sign(value: int) -> int:
    return (value > 0) - (value < 0)


def falling_jet(d: int, length: int) -> list[int]:
    """Coefficients through u^d of (2d+u) falling length."""
    coefficients = [1] + [0] * d
    for j in range(length):
        coefficients = [
            (2 * d - j) * coefficients[i]
            + (coefficients[i - 1] if i else 0)
            for i in range(d + 1)
        ]
    return coefficients


def h_column(d: int, q: int, maximum_k: int) -> list[int]:
    """H[d,k,q]=(k+2d+1+q)! gamma(k,d,k+2d+1+q)/d!.

    Generate via the centered-polynomial three-term recurrence.
    Every list stores exact Taylor coefficients, not derivatives.
    """
    require(d >= 1 and q >= 0 and maximum_k >= 0, 'invalid column indices')
    r = 2 * d + 1 + q
    previous = falling_jet(d, r)
    values = [previous[d]]
    if maximum_k == 0:
        return values
    current = [
        (2 * d - q) * previous[i] + (2 * previous[i - 1] if i else 0)
        for i in range(d + 1)
    ]
    values.append(current[d])
    for k in range(1, maximum_k):
        following = [
            (2 * d - q) * current[i]
            + (2 * current[i - 1] if i else 0)
            + k * (k + r) * previous[i]
            for i in range(d + 1)
        ]
        values.append(following[d])
        previous, current = current, following
    return values


def h_pascal(d: int, maximum_k: int, maximum_q: int) -> list[list[int]]:
    """Independent array from gamma(k+1,d,M)=2gamma(k,d,M)+gamma(k,d,M-1)."""
    row = [falling_jet(d, 2 * d + 1 + q)[d]
           for q in range(maximum_q + maximum_k + 1)]
    rows = [row[:maximum_q + 1]]
    for k in range(maximum_k):
        row = [2 * row[q + 1] + (k + 2 * d + 2 + q) * row[q]
               for q in range(len(row) - 1)]
        rows.append(row[:maximum_q + 1])
    return rows


def h_value(d: int, k: int, q: int) -> int:
    return h_column(d, q, k)[k]


def reduced_sign(d: int, k: int, q: int, value: int) -> int:
    """Sign of the positive-weight expectation of the residual polynomial."""
    if (k + d) % 2:  # sum case
        return (-1) ** q * sign(value)
    if q == 2 * d:   # symmetry zero: reduced expectation is not defined
        return 0
    return (-1) ** (q + 1) * sign(q - 2 * d) * sign(value)


def verify_rectangles() -> tuple[dict, list[dict], list[dict]]:
    report = {}
    records, thresholds = [], []
    for d, (central, tail) in PARAMETERS.items():
        maximum_k, maximum_q = central - 2, tail - 1
        pascal = h_pascal(d, maximum_k, maximum_q)
        columns = [h_column(d, q, maximum_k) for q in range(tail)]
        counts = Counter()
        for k in range(maximum_k + 1):
            reduced = []
            for q in range(tail):
                value = columns[q][k]
                require(value == pascal[k][q], f'recurrence mismatch {(d,k,q)}')
                hole = q == 2 * d and (k + d) % 2 == 0
                require((value == 0) == hole, f'unexpected zero/nonzero {(d,k,q)}')
                residues = [value % modulus for modulus in MODULI]
                if not hole:
                    require(any(residues), f'no modular witness {(d,k,q)}')
                counts['cells'] += 1
                counts['holes' if hole else 'nonzero'] += 1
                if not hole and residues[0] == 0:
                    counts['second_modulus_needed'] += 1
                rs = reduced_sign(d, k, q, value)
                reduced.append(rs)
                records.append(dict(d=d, k=k, q=q, sign=sign(value),
                                    reduced_sign=rs, mod1009=residues[0],
                                    mod1013=residues[1], symmetry_hole=int(hole)))
            # Exact summary: first negative on the left, first positive on the right.
            left_negative = next((q for q in range(2*d) if reduced[q] < 0), None)
            right_positive = next((q for q in range(2*d+1, tail) if reduced[q] > 0), tail)
            thresholds.append(dict(d=d, k=k, left_first_negative=left_negative,
                                   right_first_positive=right_positive))
        seeds = [(central, 2*d, 1)]
        sum_k, difference_k = (d-1) % 2, d % 2
        seeds.extend([(sum_k, tail, (-1) ** tail),
                      (difference_k, tail, (-1) ** (tail + 1))])
        seed_records = []
        for k, q, expected_sign in seeds:
            value = h_value(d, k, q)
            require(value == h_pascal(d, k, q)[k][q],
                    f"independent seed mismatch {(d,k,q)}")
            require(sign(value) == expected_sign, f'seed sign {(d,k,q)}')
            seed_records.append(dict(k=k, q=q, expected_sign=expected_sign,
                                     H=str(value)))
        # These negative values show minimality of the chosen central parity cutoff.
        previous_central = h_value(d, central-2, 2*d)
        require(previous_central < 0, f'central predecessor {(d,central-2)}')
        # For the smallest parity classes, check that the stated tail cutoff is sharp.
        prior = [reduced_sign(d, k, tail-1, h_value(d, k, tail-1))
                 for k in (sum_k, difference_k)]
        require(min(prior) < 0, f'tail predecessor {d}')
        report[str(d)] = dict(central_exponent=central, tail_cutoff=tail,
                             rectangle=dict(k_max=maximum_k, q_max=maximum_q),
                             counts=dict(counts), seeds=seed_records,
                             preceding_central_H=str(previous_central))
    return report, records, thresholds


def verify_original_lattice(maximum_n: int = 80) -> dict:
    """Independent differentiation recurrence; checks positivity and model bridge."""
    coefficients = {(0, 0): 1}
    tested = Counter()
    for n in range(maximum_n + 1):
        for j in range(-n, n + 1, 2):
            for k in range((n + j) // 2 + 1):
                d = (n + j) // 2 - k
                value = coefficients.get((j, k), 0)
                if j >= 0 or (j == -1 and d >= 1):
                    require(value > 0, f'bulk positivity {(n,j,k)}')
                    tested['bulk_positive_cells'] += 1
                if d >= 1 and j <= -1:
                    q = -j - 1
                    H = h_value(d, k, q)
                    require(value == math.comb(n, k) * H, f'lattice bridge {(n,j,k)}')
                    tested['lattice_bridge_cells'] += 1
                    if d <= 4:
                        hole = q == 2 * d and (k+d) % 2 == 0
                        require((value == 0) == hole, f'four-depth lattice {(n,j,k)}')
                        tested['four_depth_cells'] += 1
        next_coefficients = defaultdict(int)
        for (j, k), value in coefficients.items():
            next_coefficients[j+1, k+1] += 2 * value
            next_coefficients[j+1, k] += value
            next_coefficients[j-1, k] += j * value
            if k:
                next_coefficients[j-1, k-1] += k * value
        coefficients = {point: value for point, value in next_coefficients.items() if value}
    return dict(maximum_n=maximum_n, **tested)


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open('w', newline='', encoding='utf-8') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-data', action='store_true')
    parser.add_argument('--lattice-order', type=int, default=80)
    args = parser.parse_args()
    if args.lattice_order < 0:
        parser.error("--lattice-order must be nonnegative")
    report, records, thresholds = verify_rectangles()
    report['lattice_crosscheck'] = verify_original_lattice(args.lattice_order)
    report['moduli'] = MODULI
    report['status'] = 'PASS'
    if args.write_data:
        destination = Path(__file__).resolve().parents[1] / 'data'
        destination.mkdir(exist_ok=True)
        write_csv(destination / 'finite_certificate.csv', records)
        write_csv(destination / 'sign_thresholds.csv', thresholds)
        (destination / 'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
