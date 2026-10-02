#!/usr/bin/env python3
"""Separate explicit fourth-order log formula, plus stored-data diagnostics."""
import json
from pathlib import Path
import sympy as s
import mpmath as mp
from derive_residual import w,k,d,g,p1,p2,residual_coefficients,solve_rational_ode,cancel

# Explicit hand-expanded derivatives, avoiding the generator's jet recurrence.
a=cancel(d*s.diff(g,w)); b=cancel(d*s.diff(p1,w)-p1)
c=cancel(d*s.diff(p2,w)-2*p2)
u=cancel(d*s.diff(a,w)-a); v=cancel(d*s.diff(d,w)-d)
b1=cancel(d*s.diff(b,w)-2*b); c1=cancel(d*s.diff(c,w)-3*c)
u1=cancel(d*s.diff(u,w)-2*u); v1=cancel(d*s.diff(v,w)-2*v)
b2=cancel(d*s.diff(b1,w)-3*b1); u2=cancel(d*s.diff(u1,w)-3*u1)
v2=cancel(d*s.diff(v1,w)-3*v1)
j=k+1
ell1=k*(k-3)/2
ell2=-k*(2*k**2+3*k+1)/12
ell3=k**2*(k**2-6*k+1)/12
ell4=-(6*k**5+15*k**4+10*k**3-k)/120
A1=ell1-j*a+j**2*d/2
A2=ell2-j*b+j**2*u/2-j**3*v/6
A3=ell3-j*c+j**2*b1/2-j**3*u1/6+j**4*v1/24
A4=ell4+j**2*c1/2-j**3*b2/6+j**4*u2/24-j**5*v2/120
poly=lambda x:s.Poly(x,k,domain=s.QQ.frac_field(w))
A1,A2,A3,A4=map(poly,[A1,A2,A3,A4])
B4=A4+A1*A3+(A2*A2).mul_ground(s.Rational(1,2))+(A1*A1*A2).mul_ground(s.Rational(1,2))+(A1**4).mul_ground(s.Rational(1,24))
H3manual=s.factor(sum(coef*s.bell(power[0],w) for power,coef in B4.terms()))
A,R=residual_coefficients(4,[p1,p2]); H3=R[4]
assert cancel(H3manual-H3)==0
p3=solve_rational_ode(H3,3,9,13,2)
assert p3 is not None
assert solve_rational_ode(H3,3,9,12,2) is None
assert cancel(-w*s.diff(p3,w)+3*(w+1)*p3+H3)==0
print('Explicit fourth-order formula equals generator H3: PASS')
print('Degree-12 rational ansatz inconsistent: PASS')
print('Degree-13 rational ansatz and canonical ODE: PASS')
print('H3/w^5 limit =',s.limit(H3/w**5,w,s.oo))
print('p3/w^4 limit =',s.limit(p3/w**4,w,s.oo))

# This uses the pre-existing exact-T diagnostics. No source file is modified.
mp.mp.dps=65
f=s.lambdify(w,p3,'mpmath')
source=Path(__file__).resolve().parent.parent / 'receipts' / 'two-term-diagnostics.json'
if source.exists():
    result=[]
    for row in json.loads(source.read_text()):
        n=row['n']; wn=mp.mpf(row['w']); e2=mp.mpf(row['error_after_second'])
        predicted=f(wn)/wn**3
        e3=e2-f(wn)/n**3
        out={'n':n,'predicted_exp_minus_3w_coefficient':str(predicted),
             'observed_scaled_two_term_error':row['third_scaled_error'],
             'error_after_second':str(e2),'error_after_third':str(e3),
             'fourth_scaled_error':str(e3*mp.exp(4*wn))}
        result.append(out)
        print('n=%d predicted c3=%s; error after p3=%s' % (n,mp.nstr(predicted,14),mp.nstr(e3,14)))
    (Path(__file__).resolve().parent.parent / 'receipts' / 'p3_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
