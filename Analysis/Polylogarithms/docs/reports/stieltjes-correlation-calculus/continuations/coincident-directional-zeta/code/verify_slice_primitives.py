#!/usr/bin/env python3
"""Numerical sign/normalization checks for the Stieltjes primitive ladder."""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=55
root=Path(__file__).resolve().parents[1]
rows=[]
for a in [mp.mpf('.5'),mp.mpf('1.3')]:
    for ell in range(3):
        def primitive(x):
            return (mp.zeta(0,x,derivative=ell+1)/(2*(ell+1))
                    -mp.factorial(ell)*sum(mp.zeta(-1,x,derivative=j)/mp.factorial(j) for j in range(ell+1)))
        observed=mp.diff(primitive,a)
        predicted=-mp.zeta(0,a,derivative=ell)+(-1)**(ell+1)*mp.stieltjes(ell,a)/2
        rows.append({'a':str(a),'ell':ell,'observed':mp.nstr(observed,45),'predicted':mp.nstr(predicted,45),'absolute_error':mp.nstr(abs(observed-predicted),8)})
(root/'results'/'slice_primitive_verification.json').write_text(json.dumps({'precision':mp.mp.dps,'rigorous_certificate':False,'checks':rows},indent=2)+'\n')
print(json.dumps(rows,indent=2))
