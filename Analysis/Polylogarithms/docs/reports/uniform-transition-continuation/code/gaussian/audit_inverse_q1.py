#!/usr/bin/env python3
"""Independent inverse audit from gamma cumulants (no forward-table input).

For Y~Gamma(p,h+a), expand E f_h(exp(-Y)) about y=L.
The operator D=z*d/dz acts on the auxiliary variable z; the proposed
inverse coefficients q0,q1 remain constants during differentiation.
"""
from pathlib import Path
import json
import sympy as s

z,v,L,a,q0,q1,t=s.symbols('z v L a q0 q1 t')
D=lambda f:s.expand(z*s.diff(f,z))
D2=lambda f:D(D(f))
D3=lambda f:D(D2(f))

# Compute the small-t logarithm directly, not by importing saved U values.
# With t=1/h and e^(-y)=2*z*t, log f_h = -z+t*A+t^2*B+O(t^3).
log_kernel=s.series(s.log(s.log(1+2*z*t)/(2*z*t)),t,0,4).removeO()/t \
           -s.series(s.log(1+2*z*t),t,0,3).removeO()
assert s.expand(log_kernel).coeff(t,0)==-z
A=s.expand(log_kernel).coeff(t,1)
B=s.expand(log_kernel).coeff(t,2)
U1=A
U2=s.expand(B+A*A/2)

# p=h*L+q0+q1/h. The cumulant operator for -Delta=-(Y-L) is
# t*P1 + t^2*P2 + O(t^3). Gamma cumulants give these coefficients.
P1=lambda f:(a*L-q0)*D(f)+L*D2(f)/2
P2=lambda f:(-q1+a*q0-a*a*L)*D(f)+(q0/s.Integer(2)-a*L)*D2(f)-L*D3(f)/3
f=s.exp(-z)
C1=s.expand(s.cancel((f*U1+P1(f))/f)).subs(z,v)
Q0=s.factor(s.solve(C1,q0)[0])
C2=s.expand(s.cancel((f*U2+P1(f*U1)+P2(f)+P1(P1(f))/2)/f)).subs(z,v)
Q1=s.collect(s.expand(s.solve(C2.subs(q0,Q0),q1)[0]),L)

stored=Path(__file__).resolve().parent.parent / 'harmonic' / 'inverse_polynomials.json'
data=json.loads(stored.read_text())
checks=[s.expand(Q0-s.sympify(data['Q'][0]))==0,
        s.expand(Q1-s.sympify(data['Q'][1]))==0,
        s.expand(C1.subs(q0,Q0))==0,
        s.expand(C2.subs({q0:Q0,q1:Q1}))==0]
assert all(checks)
print(json.dumps({'method':'independent gamma-cumulant expansion',
                  'U1':str(U1),'U2':str(U2),
                  'Q0':str(Q0),'Q1':str(Q1),
                  'agrees_with_stored_inverse':[checks[0],checks[1]],
                  'exact_inverse_residual_zero':[checks[2],checks[3]]},indent=2))
