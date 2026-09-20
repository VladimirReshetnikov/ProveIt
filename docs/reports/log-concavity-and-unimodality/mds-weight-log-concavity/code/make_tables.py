#!/usr/bin/env python3
"""Regenerate the uniform-threshold table (Python 3.9+, standard library).

The threshold and prime-power comparisons are exact integer comparisons.
Decimal is used only to display the algebraic threshold. Run from any folder:
    python code/make_tables.py
"""
from __future__ import annotations
import csv
from decimal import Decimal, localcontext
from math import isqrt
from pathlib import Path


def is_prime_power(value: int) -> bool:
    if value < 2:
        return False
    for p in range(2, isqrt(value) + 1):
        if value % p == 0:
            # The first divisor is prime. Strip all its powers.
            while value % p == 0:
                value //= p
            return value == 1
    return True  # value itself is prime


def smallest_qualifying_prime_power(d: int) -> int:
    h = d * d + 2 * d - 1
    q = d + 1
    # For q>d, this polynomial is nonnegative exactly at/above Q_infinity.
    while 2 * q * q - 2 * h * q + d * h < 0 or not is_prime_power(q):
        q += 1
    return q


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    data = root / 'data'
    data.mkdir(exist_ok=True)
    rows = []
    latex = []
    with localcontext() as ctx:
        ctx.prec = 60
        for d in range(2, 11):
            h = d * d + 2 * d - 1
            threshold = (Decimal(h) + Decimal(h * (d * d - 1)).sqrt()) / 2
            q = smallest_qualifying_prime_power(d)
            rows.append((d, str(threshold), q))
            latex.append(f'{d} & {threshold:.4f} & {q} ' + r'\\')
    with (data / 'thresholds.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['d', 'Q_infinity_decimal', 'smallest_prime_power_at_or_above'])
        writer.writerows(rows)
    block = '\n'.join(latex) + '\n'
    (data / 'threshold_rows.tex').write_text(block, encoding='utf-8')
    article = root / 'article.tex'
    text = article.read_text(encoding='utf-8')
    begin = '% BEGIN GENERATED THRESHOLD ROWS\n'
    end = '% END GENERATED THRESHOLD ROWS'
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError('article.tex must contain exactly one pair of table markers')
    before, tail = text.split(begin)
    _, after = tail.split(end)
    article.write_text(before + begin + block + end + after, encoding='utf-8')
    print('Regenerated thresholds.csv, threshold_rows.tex, and the embedded article table.')


if __name__ == '__main__':
    main()
