#!/usr/bin/env python3
"""Exact rational forward/inverse coefficients and independent checks."""
from pathlib import Path
import json
import sympy as S

z,e,y = S.symbols('z e y')
K = 6
tr = lambda f, n=14: S.series(f,z,0,n).removeO().expand()
h = sum(-S.bernoulli(2*k)*z**(2*k)/(2*k*S.factorial(2*k))
        for k in range(1,K+1))
H = sum(h.coeff(z,2*k)*z**(2*k)/(2*k+1) for k in range(1,K+1))
B = 1-z*S.diff(H,z)
sc = {2*k+1:tr(B**(2*k+1)).coeff(z,2*k)/S.Integer(2*k+1)
      for k in range(K+1)}
s = sum(v*e**k for k,v in sc.items())
dc = {2*k:-sc[2*k+1]/S.Integer(2*k) for k in range(1,K+1)}
D = sum(v*e**k for k,v in dc.items())
q2 = 1+z*z*S.diff(H,z,2)
q3 = -2+z**3*S.diff(H,z,3)
q4 = 6+z**4*S.diff(H,z,4)
E0s = tr(h/2+S.log(B)-S.log(q2)/2,8)
E1s = tr(S.Rational(1,12)+z*S.diff(h,z)/12
         -(S.diff(h,z,2)/2+S.diff(h,z)**2/4)*z*z/(2*q2)
         +S.diff(h,z)*z*q3/(4*q2*q2)+q4/(8*q2*q2)
         -5*q3*q3/(24*q2**3),8)
# Polynomial substitution with small-degree truncations is much faster.
sub = lambda f: S.series(f.subs(z,s),e,0,8).removeO().expand()
E0,E1 = sub(E0s),sub(E1s)
# Independent low-order verification by the implicit saddle equation.
s6 = sum(v*e**k for k,v in sc.items() if k<=7)
assert S.series(s6-e*B.subs(z,s6),e,0,9).removeO().expand() == 0
Dcheck = S.series((s6/e)-1-S.log(s6/e)+H.subs(z,s6),e,0,8).removeO().expand()
assert S.expand(Dcheck-S.series(D,e,0,8).removeO()) == 0
# Lagrange: epsilon=eta exp(D(epsilon)).
Ds = S.series(D,e,0,8).removeO()
inv_eps = sum(S.series(S.exp(k*Ds),e,0,k).removeO().expand().coeff(e,k-1)
              *y**k/S.Integer(k) for k in (1,3,5,7))
R = S.series(y/inv_eps,y,0,8).removeO().expand()
v_eps = S.series((-Ds-E0)/(1-e*S.diff(Ds,e)),e,0,8).removeO()
v = S.series(v_eps.subs(e,inv_eps),y,0,8).removeO().expand()
assert S.series(inv_eps*S.exp(-Ds.subs(e,inv_eps))-y,y,0,9).removeO().expand()==0
# Cubic slice consistency, first inverse-m correction.
w=S.symbols('w')
# m=1/w, N=m^3; use log V and Stirling through order 1/m.
cent=S.log(1+w/4+w*w/4)
# log V - [(2m)+(m-3)log m -log(2pi)]
cubic = S.series((1/w-1)*cent-w/6+(1/w)*Ds.subs(e,w/(1+w/4+w*w/4)),w,0,2).removeO().expand()
assert cubic == S.Rational(1,4)-S.Rational(61,288)*w
out={'s':{str(k):str(v) for k,v in sc.items()},
     'D':{str(k):str(v) for k,v in dc.items()},
     'E0':str(E0),'E1':str(E1),'inverse_epsilon':str(inv_eps),
     'inverse_R':str(R),'inverse_v':str(v),
     'cubic_log_correction':str(cubic),'exact_symbolic_assertions':4}
base=Path(__file__).resolve().parents[1]
(base/'data').mkdir(exist_ok=True)
(base/'data'/'coefficients.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
