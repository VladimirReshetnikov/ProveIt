"""Exact phase classes and conditional-covariance regression."""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import json,sympy as s
rows=[]
for r in range(2,21):
    steps=list(range(-(r-1),r,2)) if r%2==0 else list(range(-(r//2),r//2+1))
    h=max(steps);inner=steps[1:-1];p=2 if r%2==0 else 1
    sigma=s.Rational(sum(v*v for v in steps),r)
    classes=Counter(tuple(Fraction(-(h+v)*k,2*h)%1 for v in inner) for k in range(2*h))
    if len(classes)!=r-1 or set(classes.values())!={p}:raise RuntimeError(('phase classes',r,classes))
    for k in range(2*h):
        # Fourier factor at n=1, N=r; all n follow by taking powers.
        theta=[Fraction(-(h+v)*k,2*h) for v in inner]
        if (-Fraction(k*r,2)-sum(theta)).denominator!=1:raise RuntimeError(('gauge phase',r,k))
    q=r-2
    C=s.eye(q)/r-s.ones(q)/(r*r)
    v=s.Matrix([s.Rational(j,r) for j in inner]) if q else s.zeros(0,1)
    Sigma=C-v*v.T/sigma
    det=Sigma.det() if q else s.S.One
    expected=s.Rational(4*h*h,r**r)/sigma
    if det!=expected or det!=s.Rational(12*(r-1),r**r*(r+1)):raise RuntimeError(('covariance determinant',r,det,expected))
    if s.cancel((2*h)**2/(sigma*det))!=r**r:raise RuntimeError(('bridge normalization',r))
    rows.append({'r':r,'height_variance':str(sigma),'mark_points':len(classes),'time_period':p,'conditional_covariance_determinant':str(det)})
out={'passed':True,'all_checks_exact':True,'records':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(rows),'alphabets')
