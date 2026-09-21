#!/usr/bin/env python3
"""Build the article's error table from exact rational CSV fields."""
from __future__ import annotations
import csv
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def upward_scientific(value: Fraction) -> str:
    if value <= 0:
        raise ValueError('An error bound must be positive.')
    with localcontext() as ctx:
        ctx.prec = 120
        ctx.rounding = ROUND_CEILING
        number = Decimal(value.numerator) / Decimal(value.denominator)
        exponent = number.adjusted()
        mantissa = number.scaleb(-exponent).quantize(Decimal('0.01'))
        if mantissa >= 10:
            mantissa /= 10
            exponent += 1
        return rf'${mantissa:.2f}\cdot10^{{{exponent}}}$'

def main() -> None:
    path = ROOT / 'data' / 'certified_intervals.csv'
    with path.open(newline='') as handle:
        values = {(r['family'], int(r['offset']), int(r['terms'])):
                  Fraction(int(r['bound_numerator']), int(r['bound_denominator']))
                  for r in csv.DictReader(handle)}
    lines = [r'\begin{tabular}{llrrr}', r'\toprule',
             r'Family & $k$ & $N=10$ & $N=20$ & $N=40$ \\', r'\midrule']
    families = [('zeta3', r'$\zeta(3)$'),
                ('zeta2_upper', r'$\zeta(2)$, upper'),
                ('zeta2_lower', r'$\zeta(2)$, lower')]
    for i, (family, label) in enumerate(families):
        if i:
            lines.append(r'\addlinespace')
        for k in [0, 1, 3]:
            entries = [label if k == 0 else '', str(k)] + [
                upward_scientific(values[family, k, n]) for n in [10, 20, 40]]
            lines.append(' & '.join(entries) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}', '']
    target = ROOT / 'data' / 'error_table.tex'
    target.write_text('\n'.join(lines))
    print(f'Wrote {target.name}; bounds rounded outward.')

if __name__ == '__main__':
    main()
