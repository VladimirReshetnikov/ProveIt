"""Exact finite controls for the strict positive-transform radial theorem.

The unbounded measure theorem is proved in the manuscript. These controls
derive the common-denominator identity, check the positive decomposition,
and compare exact rational complex differentiation with the pair formula.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import sympy as sp

B = Path(__file__).resolve().parents[1]
V = B / 'verification'
x,y,c = sp.symbols('x y c', real=True)
Dx,Dy = 1-2*c*x+x*x, 1-2*c*y+y*y
P = (x*Dy**2+y*Dx**2-(x-y)**2*(x*Dy+y*Dx))/2
positive = ((1-x)*(1-y)*((x-y)**2+x*(1-y)**2+y*(1-x)**2)/2
            +4*x*y*(1-x)*(1-y)*(1-c)+2*x*y*(x+y)*(1-c)**2)
assert sp.expand(P-positive)==0
u,v,r,h = sp.symbols('u v r h', real=True)
e = c+sp.I*h
denv = 1-2*r*c*v+r*r*v*v
numerator = e*u*(1-r*u*sp.conjugate(e))**2*(1-r*v*e)*denv
imaginary = sp.rem(sp.Poly(sp.expand(sp.im(numerator)),h),
                   sp.Poly(h*h+c*c-1,h)).as_expr()
symmetrized = (imaginary+imaginary.xreplace({u:v,v:u}))/2
assert sp.expand(symmetrized-h*P.subs({x:r*u,y:r*v})/r)==0
assert sp.expand(P.subs(y,x)-x*(1-2*c*x+x*x)**2)==0
assert sp.expand(P-positive+sp.Rational(1,100))!=0

def add(a,b): return a[0]+b[0],a[1]+b[1]
def mul(a,b): return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def scale(a,k): return a[0]*k,a[1]*k
def inv(a):
    d=a[0]**2+a[1]**2
    return a[0]/d,-a[1]/d
def poly(X,Y,C):
    D1,D2=1-2*C*X+X*X,1-2*C*Y+Y*Y
    return (X*D2*D2+Y*D1*D1-(X-Y)**2*(X*D2+Y*D1))/2

atoms=[[(F(0),F(1))],[(F(1),F(1))],[(F(1,3),F(7))],
       [(F(0),F(2)),(F(1),F(3))],
       [(F(1,5),F(1)),(F(4,5),F(2))],
       [(F(0),F(2)),(F(1,2),F(3)),(F(1),F(5))],
       [(F(j,7),F(j+1)) for j in range(8)],
       [(F(j,11),F(12-j)) for j in range(12)]]
parameters=[F(1,4),F(1,2),F(1),F(2),F(4)]
counts=dict(atomic_pair_equalities=0,quantitative_bounds=0,
            strict_positive_cases=0,constant_zero_cases=0,
            prescribed_outside_radius_counterexamples=0)
for measure in atoms:
    moments=[sum(w*u**j for u,w in measure) for j in range(3)]
    for rho in [F(1,8),F(1,4),F(1,2),F(3,4),F(1)]:
        for t in parameters:
            C,H=(1-t*t)/(1+t*t),2*t/(1+t*t)
            E=(C,H);z=scale(E,rho);Q=(F(0),F(0));Qprime=Q
            for U,w in measure:
                q=inv((1-U*z[0],-U*z[1]))
                Q=add(Q,scale(q,w));Qprime=add(Qprime,scale(mul(q,q),w*U))
            velocity=mul(mul(E,Qprime),inv(Q))[1]
            norm=Q[0]**2+Q[1]**2
            pairing=F(0)
            for U,w in measure:
                for W,k in measure:
                    X,Y=rho*U,rho*W
                    D1,D2=1-2*C*X+X*X,1-2*C*Y+Y*Y
                    pairing+=w*k*poly(X,Y,C)/(D1*D1*D2*D2)
            assert velocity==H*pairing/(rho*norm)
            counts['atomic_pair_equalities']+=1
            lower=4*rho*rho*H**3*(1-C)**2*moments[1]*moments[2]/((1+rho)**8*moments[0]**2)
            assert velocity>=lower
            counts['quantitative_bounds']+=1
            if moments[1]:
                assert velocity>0;counts['strict_positive_cases']+=1
            else:
                assert velocity==0;counts['constant_zero_cases']+=1

for q in range(1,41):
    rho=1+F(1,q);v=(1+rho**-2)/2
    for t in parameters:
        C,H=(1-t*t)/(1+t*t),2*t/(1+t*t)
        E=(C,H);z=scale(E,rho)
        Q=mul((1-v*z[0],-v*z[1]),inv((1-z[0],-z[1])))
        Qprime=scale(mul(inv((1-z[0],-z[1])),inv((1-z[0],-z[1]))),1-v)
        direct=mul(mul(E,Qprime),inv(Q))[1]
        expected=(1-v)*(1-rho*rho*v)*H/((1-2*rho*C+rho*rho)*(1-2*rho*v*C+rho*rho*v*v))
        assert direct==expected<0
        counts['prescribed_outside_radius_counterexamples']+=1

record=dict(status='PASS',symbolic_identities=3,corrupted_polynomial_controls=1,
            counts=counts,scope='Finite exact symbolic and rational controls; the continuum theorem uses the displayed positive decomposition and measure differentiation proof.')
(V/'stieltjes-radial-certificates.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
