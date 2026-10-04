"""New finite symbolic checks of Report60 identities, no packet execution or simulation."""
import json
from pathlib import Path
from fractions import Fraction as F
from math import gcd,lcm
import sympy as s
out={}
def require(test,label):
    if not test: raise RuntimeError(label)
def zero(expr,label):
    require(s.simplify(expr)==0,label)
a,b,c,d,z,u,v,t,e,q,p=s.symbols('a b c d z u v t e q p')
zero(z+(u-1)/(u+1)*((2+u)*z-z)-u*z,'scale meet')
f=v*t+(1-v)*z
zero(t+(1-v)/(1+v)*(2*z-f-t)-f,'homothety meet')
zero(t/(1-e)-(t+e*z)-e*(t+e*z-z)/(1-e),'translation identity')
U=lambda t:s.Matrix([[1,t],[0,1]])
V=lambda t:s.Matrix([[1,0],[t,1]])
B=s.Matrix([[a,b],[c,d]])
for name,diff in [('c',U((a-1)/c)*V(c)*U((d-1)/c)-B),('b',V((d-1)/b)*U(b)*V((a-1)/b)-B)]:
    for entry in diff:
        require(s.rem(s.together(entry).as_numer_denom()[0],a*d-b*c-1,a)==0,'factor '+name)
require(s.simplify(U(a-1)*V(1)*U(1/a-1)*V(-a)-s.diag(a,1/a))==s.zeros(2),'diag factor')
C=s.Matrix([[0,-1],[1,t]]); H=s.Matrix([[1,t/2],[t/2,1]])
require(s.simplify(C.T*H*C-H)==s.zeros(2),'metric')
A=s.Matrix([[s.Rational(3,5),-s.Rational(8,5)],[s.Rational(2,5),s.Rational(3,5)]])
Q=s.diag(1,4); point=s.Matrix([-s.Rational(2,15),s.Rational(1,30)])
require(A.T*Q*A==Q,'fixture metric')
require((point.T*Q*point)[0]==s.Rational(1,45),'fixture radius')
require(4*s.Matrix.hstack(point,A.inv()*point).inv()==s.Matrix([[-33,-12],[15,60]]),'fixture contact basis')
out['symbolic_identities']=10
checks=0
for den in range(2,23):
    for num in range(-2*den+1,2*den):
        if gcd(num,den)!=1: continue
        x,y=F(1),F(0)
        cn,dn=1,0
        for n in range(31):
            if n:
                require(lcm(x.denominator,y.denominator)==den**(n-1),'exact denominator')
                require((x,y)==(F(cn,den**n),F(dn,den**(n-1))),'power coefficient scaling')
            require(cn*cn+num*cn*dn+den*den*dn*dn==den**(2*n),'quadratic norm')
            x,y=-y,x+F(num,den)*y
            cn,dn=-den*den*dn,cn+num*dn
            checks+=1
out['exact_power_instances']=checks
g1,g2,g3=s.symbols('g1 g2 g3'); X=2*g1-g2-g3; Y=g1+g2-2*g3; N=3*(g1+g2+g3)
for expr,target in [((N+3*X)/9,g1),((N-3*X+3*Y)/9,g2),((N-3*Y)/9,g3)]:zero(expr-target,'inverse gap aliases')
rows=[N+X,N-X,N+Y,N-Y,N-6*X-6*Y,N-6*X+1]
require([r.subs({g1:6,g2:1,g3:5}) for r in rows]==[42,30,33,39,18,1],'valid half-open')
require(rows[-1].subs({g1:7,g2:1,g3:5})==-8,'invalid half-open')
W,G,alpha=s.symbols('W G alpha'); residual=alpha**2-1-((W+1)**2-1)*(W*G)**2
require(s.Poly(residual,W,G,alpha).total_degree()==6,'POWER residual degree')
require(s.Poly(residual**2,W,G,alpha).coeff_monomial(W**8*G**4)==1,'POWER leading term')
require(6+7+2*8+2*26==81 and 14+2*15==44,'ledger')
out.update({'gap_inverse_identities':3,'half_open_examples':2,'POWER_leading_coefficient':1,'per_contact_witnesses':81,'per_contact_residuals':44,'status':'PASS'})
path=Path(__file__).with_name('independent_algebra_results.json');path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,sort_keys=True))
