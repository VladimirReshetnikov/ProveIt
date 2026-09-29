"""Generate LaTeX tables from the exact checked data (not part of the proof)."""
from pathlib import Path
from fractions import Fraction as Q
import json
BASE=Path(__file__).resolve().parent.parent
D=json.loads((BASE/'data/profiles.json').read_text())
V=json.loads((BASE/'data/verification.json').read_text())
U=json.loads((BASE/'data/upper_N18.json').read_text())
NAMES=D['names']; out=BASE/'tex'

def save(name,lines): (out/name).write_text('\n'.join(lines)+'\n')
rows=[r'\begin{tabular}{@{}lrrr@{}}',r'\toprule',r'Coordinate & Numerator of $v_i$ & $10^{12}$-scaled slack & $10^6$-scaled tail\\',r'\midrule']
r=next(x for x in V['upper'] if x['N']==18)
for i,n in enumerate(NAMES):
 rows.append(f'${n}$ & {U["numerators"][i]:,} & {r["residual_lower_numerators_1e12"][i]:,} & {(Q(r["tail_budgets"][i])*10**6).__floor__():,} \\\\')
rows += [r'\bottomrule',r'\end{tabular}'];save('upper_table.tex',rows)
for start,end in [(1,9),(10,18)]:
 rows=[r'\begin{tabular}{@{}l'+'r'*(end-start+1)+r'@{}}',r'\toprule',' & '.join(['$n$']+[str(n) for n in range(start,end+1)])+r'\\',r'\midrule']
 rows.append('$A_n$ & '+' & '.join(str(D['polyominoes'][n]) for n in range(start,end+1))+r'\\')
 rows.append(r'\midrule')
 for i,name in enumerate(NAMES):
  rows.append('$'+name.upper()+'$ & '+' & '.join(str(D['counts'][i][n]) for n in range(start,end+1))+r'\\')
 rows += [r'\bottomrule',r'\end{tabular}'];save(f'profiles_{start}_{end}.tex',rows)
rows=[r'\begin{tabular}{@{}lrl@{}}',r'\toprule',r'Row & $r_i$ & Monomial weights, in the order in (\ref{eq:map})\\',r'\midrule']
C=json.loads((BASE/'data/dual_original.json').read_text());k=0
from model import TERMS
for i,row in enumerate(TERMS):
 m=C['weights'][k:k+len(row)];k+=len(row)
 rows.append(f'${NAMES[i]}$ & {C["row_sums"][i]:,} & '+', '.join(f'{n:,}' for n in m)+r'\\')
rows += [r'\bottomrule',r'\end{tabular}'];save('dual_table.tex',rows)
E=json.loads((BASE/'data/critical_estimates.json').read_text())
rows=[r'\begin{tabular}{@{}rrr@{}}',r'\toprule',r'Prefix size $N$ & Estimated equality growth & Certified upper bound\\',r'\midrule',r'$1$--$6$ & $4.523499228$ & $4.5235$ (original certificate)\\']
for n in range(7,19):
 c=json.loads((BASE/f'data/upper_N{n}.json').read_text());rows.append(f'{n} & ${1/E[n-1][17]:.9f}$ & ${float(Q(c["growth_upper"])):.4f}$'+r'\\')
rows += [r'\bottomrule',r'\end{tabular}'];save('progress_table.tex',rows)
