#!/usr/bin/env python3
"""Regenerate the small TeX tables from the checked JSON data."""
from pathlib import Path
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
import json
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'data/verification.json').read_text())
rows=[]
for n in range(1,7):
    cols=[str(n)]
    for seq,shift in [('A088714','0'),('A088714','1'),('A088713','0'),('A088713','1')]:
        cols.append(f"{int(r['leading_Hankel_determinants'][seq][shift][n-1]):,}")
    rows.append(' & '.join(cols)+r' \\')
(ROOT/'data/hankel_table.tex').write_text('\n'.join(rows)+'\n')
rows=[]
for d in r['diagnostics']:
    rows.append(f"{d['n']} & {d['A088714_ratio_scaled']:.6f} & "
                f"{d['A088713_ratio_scaled']:.6f}"+r' \\')
(ROOT/'data/ratio_table.tex').write_text('\n'.join(rows)+'\n')
o=json.loads((ROOT/'data/orbit_bounds.json').read_text())
rows=[]
for d in o['records']:
    with localcontext() as ctx:
        ctx.prec=100
        lo=Decimal(d['normalized_lower']).quantize(Decimal('1e-12'),rounding=ROUND_FLOOR)
        hi=Decimal(d['normalized_upper']).quantize(Decimal('1e-12'),rounding=ROUND_CEILING)
    rows.append(rf"{d['k']} & {float(d['log_s_lower']):.6f} & $[{lo},\,{hi}]$"+r' \\')
(ROOT/'data/orbit_table.tex').write_text('\n'.join(rows)+'\n')
