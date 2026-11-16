#!/usr/bin/env python3
"""Compare all stored exact tensors from the independent arithmetic engines."""
import json
from pathlib import Path
import sympy as sp

root = Path(__file__).resolve().parents[1]
cs = root/'certificates'
small = json.loads((cs/'stdlib_results.json').read_text())
large = json.loads((cs/'sympy_results.json').read_text())
r,x,a,m,q = sp.symbols('r x a m q')
vs = (r,x,a,m,q)
ds = (sp.Integer(2),r*r+a*a*x*x,r*r-2*m*r+a*a+q*q,1-x*x)
def decode(z):
    p = sum(sp.Integer(c)*sp.prod(v**e for v,e in zip(vs,ex)) for ex,c in z['numerator'])
    d = sp.prod(v**e for v,e in zip(ds,z['denominator_powers_2_S_D_s']))
    return p/d
checked = 0
for key in ('ricci','field','maxwell_density'):
    for i in range(4):
        for j in range(4):
            residual = sp.cancel(decode(small[key][i][j])-sp.sympify(large[key][i][j]))
            if residual!=0: raise ValueError((key,i,j,str(residual)))
            checked += 1
out={'status':'PASS','compared_components':checked,'tensors':['ricci','field','maxwell_density']}
(cs/'engine_comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'PASS: {checked} tensor components agree exactly between the two engines')
