"""Generate the small TeX tables from the reproducibility data."""
import csv
import json
from pathlib import Path
from decimal import Decimal
from kbonacci_parity import count_prefix
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
h = {k: count_prefix(k, 12) for k in range(2, 7)}
lines = [r'\begin{center}',r'\begin{tabular}{@{}rrrrrr@{}}',r'\toprule',
         r'$n$ & $h_2(n)$ & $h_3(n)$ & $h_4(n)$ & $h_5(n)$ & $h_6(n)$\\',r'\midrule']
for n in range(13):
    lines.append(' & '.join([str(n)]+[str(h[k][n]) for k in range(2,7)])+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(DATA/'initial_table.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{center}',r'\begin{tabular}{@{}rrrr@{}}',r'\toprule',
         r'$k$ & $\lambda_k$ & $C_k$ & $\rho_k$\\',r'\midrule']
for row in list(csv.DictReader((DATA/'growth.csv').open()))[:7]:
    vals = [row['k']]+[f'{Decimal(row[key]):.12f}' for key in ['lambda','C','rho_multinacci']]
    lines.append(' & '.join(vals)+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(DATA/'growth_table.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{center}',r'\begin{tabular}{@{}rrr@{}}',r'\toprule',
         r'$k$ & Decimal digits of $h_k(10000)$ & $h_k(10^{12})\bmod 1000000007$\\',r'\midrule']
for k,row in json.loads((DATA/'large_values.json').read_text()).items():
    lines.append(f"{k} & {row['decimal_digits']} & {row['h_10pow12_mod_1000000007']}"+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(DATA/'large_table.tex').write_text('\n'.join(lines)+'\n')
