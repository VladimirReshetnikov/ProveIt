#!/usr/bin/env python3
"""Check parent residuals under the positive scaled-main-root embedding."""
import runpy
from pathlib import Path
D=Path(__file__).resolve().parent
old=runpy.run_path(str(D.parent/'adaptive-square-sums41-quartic/verify_degree.py'))
new=runpy.run_path(str(D/'verify_degree.py'))
P=new['P'];g=new['g']
replacement={name:g[name] for name in new['names']}
replacement['dValueVariable']=g['mainScaleVariable']*g['mainQuotient']
replacement['varphiSquareVariable']=g['mainScaleVariable']*g['mainScaleVariable']
def substitute(poly):
    total=P.lift(0)
    for monomial,coefficient in poly.d.items():
        term=P.lift(coefficient)
        for name,exponent in zip(old['names'],monomial):
            for _ in range(exponent):term=term*replacement[name]
        total=total+term
    return total
for name in old['factors_names']:
    actual=substitute(old['g'][name])
    if name=='varphiSquareDifference':
        expected=P.lift(0)
    elif name=='A1':
        expected=g['mainScaleVariable']*g['mainScaleVariable']*g['A1']
    else:
        expected=g[name]
    if actual!=expected:
        raise ValueError(('residual mismatch',name))
if len(old['factors_names'])!=32 or len(new['factors_names'])!=31:
    raise ValueError('residual count')
print('PASS: 30 unchanged residuals, scaled main norm and eliminated square residual')
