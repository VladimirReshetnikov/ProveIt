import sympy as s
import json
from pathlib import Path
r,t,e,h,x,z,u,F,c=s.symbols('r t e h x z u F c', nonzero=True)
B1=1/(1-t)-1/(1-t)**2
B2=s.Rational(3,2)/(1-t)**2-4/(1-t)**3+s.Rational(5,2)/(1-t)**4
K0=-s.log(1-t)
t0=1-r
t1=s.factor(-s.diff(B1,t).subs(t,t0)/s.diff(K0,t,2).subs(t,t0))
assert s.simplify(t1-(2/r-1))==0
# Stationarity means the unknown second saddle displacement cancels from A.
A1=s.factor(r*(B2+s.diff(B1,t)*t1+s.diff(K0,t,2)*t1**2/2).subs(t,t0))
var1=s.factor((s.diff(B1,t,2)+s.diff(K0,t,3)*t1).subs(t,t0))
pref1=s.factor(-t1/t0-var1*r*r/2)
Q1lim=s.factor(s.Rational(6,8)-s.Rational(5,24)*4-1/(t0/r)-1/(t0/r)**2)
c1=s.factor(A1+pref1+Q1lim/r)
want=-(r**4+10*r**3-17*r**2+24*r-6)/(12*r**3*(r-1)**2)
assert s.simplify(c1-want)==0
# Derive H3 using F'=uF-c and differentiation, not a copied kernel formula.
def D(expr):
    return s.expand(s.diff(expr,u)+s.diff(expr,F)*(u*F-c))
H3=s.expand(-D(D(D(F)))+3*D(F))
assert s.simplify(H3-((u*u-1)*c-u**3*F))==0
central=s.expand((x+x**3/6)*F-(1+x*x/2)*(x*F-c)-H3.subs(u,x)/3)
assert s.simplify(central-(x*x+8)*c/6)==0
# Verify general degree parity and no constant Hermite term through R=10.
v,eta=s.symbols('v eta')
parity={}
for R in range(11):
    # Use generic nonzero cumulants = r!, enough to retain all allowed monomials.
    exp_poly=sum(v**(j+2)*eta**j for j in range(1,R+1))
    ans=0
    term=s.Integer(1)
    for n in range(R+1):
        if n: term=s.Poly(s.expand(term*exp_poly/n),eta)
        if n: term=sum(co*eta**po[0] for po,co in term.terms() if po[0]<=R)
        ans+=term
    C=s.expand(ans).coeff(eta,R)
    degrees=[po[0] for po,co in s.Poly(C,v).terms() if co]
    assert all(d%2==R%2 for d in degrees)
    assert R==0 or 0 not in degrees
    parity[R]=degrees
out={'saddle_first_displacement':str(t1),'variance_first_correction':str(var1),'exponent_first_correction':str(A1),'prefactor_first_correction':str(pref1),'Q1_limit':str(Q1lim),'c1':str(c1),'H3':str(H3),'P1_phi0_coefficient':str(s.factor(central/c)),'parity_degrees':parity,'status':'PASS'}
Path(__file__).with_name('recomputed.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
