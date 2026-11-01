#!/usr/bin/env python3
"""Check parent residuals under the positive scaled-root embedding."""
import runpy
from pathlib import Path
D=Path(__file__).resolve().parent
old=runpy.run_path(str(D.parent/'adaptive-square-sums42-quartic/verify_degree.py'))
new=runpy.run_path(str(D/'verify_degree.py'))
P=new['P'];g=new['g']
replacement={name:g[name] for name in new['names']}
replacement['zValueVariable']=g['scaleVariable']*g['firstQuotient']
replacement['psiSquareVariable']=g['scaleVariable']*g['scaleVariable']
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
    if name=='psiSquareDifference':
        expected=P.lift(0)
    elif name=='A0':
        expected=g['scaleVariable']*g['scaleVariable']*g['A0']
    else:
        expected=g[name]
    if actual!=expected:
        raise ValueError(('residual mismatch',name))
if len(old['factors_names'])!=33 or len(new['factors_names'])!=32:
    raise ValueError('residual count')
print('PASS: 31 unchanged residuals, scaled first norm and eliminated square residual')
