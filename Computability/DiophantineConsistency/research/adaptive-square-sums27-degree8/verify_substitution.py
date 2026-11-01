#!/usr/bin/env python3
"""Verify every parent residual after eliminating the named ell product input."""
import runpy
from pathlib import Path
D=Path(__file__).resolve().parent
old=runpy.run_path(str(D.parent/'adaptive-square-sums28-degree8/verify_degree.py'))
new=runpy.run_path(str(D/'verify_degree.py'))
P=new['P'];g=new['g'];replacement={name:g[name] for name in new['names']}
replacement['ellProductVariable']=g['g40']
def substitute(polynomial):
 total=P.lift(0)
 for monomial,coefficient in polynomial.d.items():
  term=P.lift(coefficient)
  for name,exponent in zip(old['names'],monomial):
   for _ in range(exponent):term=term*replacement[name]
  total=total+term
 return total
assert [n for n in old['factors_names'] if n!='ellProductDifference']==new['factors_names']
for name in old['factors_names']:
 expected=P.lift(0) if name=='ellProductDifference' else g[name]
 if substitute(old['g'][name])!=expected:raise ValueError(('residual mismatch',name))
print('PASS: all parent residuals match; eliminated ell product residual becomes zero')
