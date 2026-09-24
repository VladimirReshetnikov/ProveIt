#!/usr/bin/env python3
"""Make the article's LaTeX tables from diagnostics.csv (no network)."""
from pathlib import Path
import csv
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 50


def sci(value: str, digits: int = 5) -> str:
    x = mp.mpf(value)
    if x == 0:
        return '$0$'
    exponent = int(mp.floor(mp.log10(abs(x))))
    coefficient = x / mp.power(10, exponent)
    return r'$' + mp.nstr(coefficient, digits) + r'\times10^{' + str(exponent) + r'}$'


def main() -> None:
    with (ROOT/'data/diagnostics.csv').open() as f:
        rows = {int(row['n']): row for row in csv.DictReader(f)}
    lines = [r'\begin{tabular}{r r r r}', r'\toprule',
             r'$n$ & $(B_n-a(n))/B_n$ & $F(n)/a(n)-1$ & $F_1(n)/a(n)-1$ \\',
             r'\midrule']
    for n in [10, 20, 50, 100, 200, 400, 1000, 2000]:
        row = rows[n]
        lines.append(str(n)+' & '+' & '.join(sci(row[k]) for k in
                     ['deficit','F_over_a_minus_1','F1_over_a_minus_1'])+r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/'data/table_main.tex').write_text('\n'.join(lines)+'\n')
    lines = [r'\begin{tabular}{r r r r}', r'\toprule',
             r'$n$ & $n(D_n/S(n,K_n)-1)$ & $T(n)/D_n-1$ & $T_1(n)/D_n-1$ \\',
             r'\midrule']
    for n in [50,51,100,101,400,401,2000,2001]:
        row = rows[n]
        lines.append(str(n)+' & $'+mp.nstr(mp.mpf(row['n_tail_endpoint_excess']),8)+'$ & '+
                     ' & '.join(sci(row[k]) for k in
                     ['D0_over_D_minus_1','D1_over_D_minus_1'])+r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/'data/table_tail.tex').write_text('\n'.join(lines)+'\n')
    print('Wrote table_main.tex and table_tail.tex')


if __name__ == '__main__':
    main()
