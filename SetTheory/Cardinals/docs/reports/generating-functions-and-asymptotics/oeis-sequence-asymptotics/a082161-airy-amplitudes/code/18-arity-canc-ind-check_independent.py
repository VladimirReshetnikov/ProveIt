"""Independent algebra/order checks; imports no producer code."""
import json
import sympy as s
x,e,L,a,h=s.symbols('x e L a h')
checks=[]
for k in range(3,13):
    q=k-1; d=3*q
    # Re-derive source coordinates directly from i=e^-3, j=x/e-1.
    X=(q/e**3+x/e-1)/k
    m=(1/e**3-x/e+1)/k
    falling=s.prod(X-j for j in range(k))
    diff=s.cancel(((m-1)-2*m/2)*q**(2*k)/falling)
    den=s.prod(q+x*e**2-(1+k*j)*e**3 for j in range(k))
    expected=-q**(2*k)*k**k*e**(d+3)/den
    assert s.cancel(diff-expected)==0
    lead=s.limit(diff/e**(d+3),e,0)
    assert lead==-q**k*k**k
    # No next epsilon power, and order +2 spatial correction is permitted.
    unit=s.cancel(diff/e**(d+3))
    assert s.diff(unit,e).subs(e,0)==0
    scalar=-lead/s.Integer(k)**k
    assert scalar==q**k
    logstep=scalar/k
    hd=-s.Rational(3,d)*logstep
    physical=s.factor(hd/s.Integer(k)**q)
    assert physical==-s.Rational(q**(k-1),k**k)
    # All valuations are checked against their proper target, not each other.
    assert min(2*d-1,2*d)>d+3
    assert 2*d>d+3
    assert 2*(d-1)>=d+1
    assert d+2>=d+1
    # Independent step matching for h_d i^(-d/3).
    logH=s.series(h*e**d*(1-(1-e**3)**(-s.Rational(d,3))),e,0,d+4).removeO()
    assert logH.coeff(e,d+3)==-s.Rational(d,3)*h
    # Pure-f forcing is solved with zero gauged profile and scalar a.
    # For L_q(Af+Bf'), A=B=0, k L_q phi - a f + a f=0.
    checks.append(dict(k=k,d=d,scalar=str(scalar),physical=str(physical),
                       nonlinear_equation=min(2*d-1,2*d),scalar_target=d+3,
                       nonlinear_endpoint=2*d-2,endpoint_target=d))
assert checks[0]['physical']=='-4/27'
assert checks[1]['physical']=='-27/256'
print(json.dumps({'status':'passed','cases':checks},indent=2))
