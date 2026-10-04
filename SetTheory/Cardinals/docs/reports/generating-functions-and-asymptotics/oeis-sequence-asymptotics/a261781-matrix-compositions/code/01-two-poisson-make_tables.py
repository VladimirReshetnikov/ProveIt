#!/usr/bin/env python3
"""Create LaTeX table bodies from the checked CSV files (standard library)."""
from pathlib import Path
import csv
ROOT=Path(__file__).resolve().parents[1]
def sci(x):
    mant,ex=f'{float(x):+.3e}'.split('e')
    return '$'+mant+r'\times10^{'+str(int(ex))+'}$'
rows=list(csv.DictReader((ROOT/'results/a261784_asymptotics.csv').open()))
with (ROOT/'results/error_table.tex').open('w') as f:
    for r in rows:
        if int(r['m']) in [10,20,50,100,200]:
            f.write(r['m']+' & '+' & '.join(sci(r[f'relative_error_order_{j}']) for j in range(4))+r' \\'+'\n')
rows=list(csv.DictReader((ROOT/'results/coupon_transition.csv').open()))
with (ROOT/'results/coupon_table.tex').open('w') as f:
    for r in rows:
        if abs(float(r['s_actual']))<.1:
            f.write(r['k']+' & '+r['n']+' & '+' & '.join(f'{float(r[x]):.9f}' for x in ['probability_exact','Poisson_approximation','corrected_approximation'])+r' \\'+'\n')
rows=list(csv.DictReader((ROOT/'results/stirling_defect.csv').open()))
if not {10,50,200}.issubset({int(r['m']) for r in rows}):
    raise SystemExit('Rebuilding article tables requires verify.py --max-m 200 or larger.')
with (ROOT/'results/defect_table.tex').open('w') as f:
    for ell in range(6):
        sub=[r for r in rows if int(r['defect'])==ell]
        vals=[next(r for r in sub if int(r['m'])==m)['probability'] for m in [10,50,200]]
        f.write(str(ell)+' & '+' & '.join(f'{float(v):.9f}' for v in vals+[sub[0]['Poisson_limit']])+r' \\'+'\n')
