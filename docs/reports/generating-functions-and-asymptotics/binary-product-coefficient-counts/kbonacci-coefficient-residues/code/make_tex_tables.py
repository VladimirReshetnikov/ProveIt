"""Generate the small TeX table fragments the article \\input{}s.

Notation follows the merged article: a_k(n) is the odd-coefficient count,
rho_k its growth constant, C_k the leading constant, beta_k the k-bonacci
growth constant. The CSV column names in data/growth.csv are inherited from
the signed-cancellation package, where rho_k was called lambda and beta_k
was called rho_multinacci.
"""
import csv
import json
from pathlib import Path
from decimal import Decimal
from kbonacci_parity import count_prefix

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'

h = {k: count_prefix(k, 12) for k in range(2, 7)}
lines = [r'\begin{center}', r'\begin{tabular}{@{}rrrrrr@{}}', r'\toprule',
         r'$n$ & $a_2(n)$ & $a_3(n)$ & $a_4(n)$ & $a_5(n)$ & $a_6(n)$\\',
         r'\midrule']
for n in range(13):
    lines.append(' & '.join([str(n)] + [str(h[k][n]) for k in range(2, 7)]) + r'\\')
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
(DATA / 'initial_table.tex').write_text('\n'.join(lines) + '\n')

lines = [r'\begin{center}', r'\begin{tabular}{@{}rrrr@{}}', r'\toprule',
         r'$k$ & $\rho_k$ & $C_k$ & $\beta_k$\\', r'\midrule']
for row in list(csv.DictReader((DATA / 'growth.csv').open()))[:7]:
    vals = [row['k']] + [f"{Decimal(row[key]):.12f}"
                         for key in ['lambda', 'C', 'rho_multinacci']]
    lines.append(' & '.join(vals) + r'\\')
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
(DATA / 'growth_table.tex').write_text('\n'.join(lines) + '\n')

lines = [r'\begin{center}', r'\begin{tabular}{@{}rrr@{}}', r'\toprule',
         r'$k$ & Decimal digits of $a_k(10000)$ & '
         r'$a_k(10^{12})\bmod 1000000007$\\', r'\midrule']
for k, row in json.loads((DATA / 'large_values.json').read_text()).items():
    lines.append(f"{k} & {row['decimal_digits']} & "
                 f"{row['h_10pow12_mod_1000000007']}" + r'\\')
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
(DATA / 'large_table.tex').write_text('\n'.join(lines) + '\n')

print('wrote initial_table.tex, growth_table.tex, large_table.tex')
