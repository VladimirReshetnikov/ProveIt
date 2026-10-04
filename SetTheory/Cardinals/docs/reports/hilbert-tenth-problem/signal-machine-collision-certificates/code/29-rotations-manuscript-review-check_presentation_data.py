#!/usr/bin/env python3
"""Fresh rational presentation-data checks; source files are read-only."""
from pathlib import Path
from fractions import Fraction as F
import re
import json
import hashlib
from itertools import combinations

HERE=Path(__file__).resolve().parent
ROOT=Path('/workspace/shared/five-signal-rotation-family59-release-20261004')
SCI=Path('/workspace/shared/five-signal-rotation-family59-20261004')
table=(ROOT/'manuscript/fixture-table.tex').read_text()
rows=re.findall(r'\$\((-?\d+),(-?\d+),(\d+)\)\$ & (\d+) & (\d+) & (\d+) & (\d+) & (\d+) & \$(\d+/\d+)\$',table)
assert len(rows)==15
for a,b,c,nx,ny,m1,m2,guards,rho in rows:
    for scale,count in [('1over1',m1),('1over2',m2),('2over1',m2)]:
        data=json.loads((SCI/f'evidence/a{a}_b{b}_c{c}_scale{scale}.json').read_text())
        assert [int(nx),int(ny)]==[data['parameters']['Nx'],data['parameters']['Ny']]
        assert int(count)==data['counts']['events']
        assert int(guards)==data['counts']['guards']
        assert F(rho)==F(data['rho_squared'])

data=json.loads((SCI/'evidence/a3_b4_c5_scale1over2.json').read_text())
guards=[tuple(map(F,g['row'])) for g in data['guards']]
vertices=set()
for (h,u,v),(h2,u2,v2) in combinations(guards,2):
    det=u*v2-u2*v
    if det:
        p=((v*h2-v2*h)/det,(u2*h-u*h2)/det)
        if all(hh+uu*p[0]+vv*p[1]>=0 for hh,uu,vv in guards): vertices.add(p)
assert len(vertices)==7
fig=(ROOT/'manuscript/geometry-figure.tex').read_text()
coordinate=r'\((-?\d+\.\d+),(-?\d+\.\d+)\)'
plotted=[tuple(map(F,p)) for p in re.findall(coordinate,fig.split('\\fill[gray!12]',1)[1].split('cycle;',1)[0])]
eps=F(1,2*10**10)
def close(p,q): return all(abs(a-b)<=eps for a,b in zip(p,q))
assert len(plotted)==len(vertices)
assert all(sum(close(p,q) for q in vertices)==1 for p in plotted)
assert all(sum(close(p,q) for p in plotted)==1 for q in vertices)
assert F(data['rho_squared'])==F(1,65)
for r in re.findall(r'circle\[radius=(0\.124\d+)\]',fig):
    r=F(r)
    assert (r-eps)**2<=F(1,65)<=(r+eps)**2
assert [list(map(F,p)) for p in data['tangent_points']]==[[F(4,65),F(-7,65)]]
right=fig.split('\\begin{scope}[xshift=5.45cm]',1)[1]
coords=[tuple(map(F,p)) for p in re.findall(r'\\draw\[red[^\]]+\] '+coordinate,right)]
assert len(coords)==14
p=(F(4,65),F(-7,65))
for q in coords:
    assert close(p,q)
    p=(F(3,5)*p[0]+F(4,5)*p[1],-F(4,5)*p[0]+F(3,5)*p[1])
receipt={'status':'PASS','table_rotation_rows':len(rows),'fixture_table_values_matched':45,'figure_feasible_vertices':len(vertices),'figure_inverse_orbit_points':len(coords),'exact_figure_radius_squared':'1/65','decimal_absolute_tolerance_per_coordinate':str(eps),'figure_exact_vertices':[[str(v) for v in p] for p in sorted(vertices)],'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'PRESENTATION_DATA_RECEIPT.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,indent=2,sort_keys=True))
