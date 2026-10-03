"""Independent finite checks; these do not replace the uniform remainder proof."""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
import mpmath as mp
import sympy as s
mp.mp.dps=65
x,r,F,c=s.symbols('x r F c')
H3=(x*x-1)*c-x**3*F
central=s.expand((x+x**3/6)*F-(1+x*x/2)*(x*F-c)-H3/3)
assert s.simplify(central-(x*x+8)*c/6)==0
c1=(2*r*r-4*r+1)/(2*r**3)-(r*r-3*r+1)/(r*r*(r-1))+(-s.Rational(1,12)-r/(1-r)**2)/r
wanted=-(r**4+10*r**3-17*r*r+24*r-6)/(12*r**3*(r-1)**2)
assert s.factor(c1-wanted)==0

def exact_success(m,k):
    q=[(-1)**j*factorial(m-1)//factorial(m-1-j) for j in range(m)]
    poly=[1]
    for _ in range(k):
        out=[0]*(len(poly)+m-1)
        for i,a in enumerate(poly):
            for j,b in enumerate(q):out[i+j]+=a*b
        poly=out
    den=factorial(k+len(poly)-1)
    total=sum(a*(den//factorial(k+j)) for j,a in enumerate(poly))
    return Fraction(m**k*total,den)

def saddle_approx(m,k,R):
    def raw(t,j):
        return mp.quad(lambda y:y**j*mp.exp(t*y)*(1-y/m)**(m-1),[0,m])
    rho=mp.mpf(k)/m
    t=mp.mpf(0) if k==m+1 else mp.findroot(lambda t:raw(t,1)/raw(t,0)-1/rho,(1-rho,1-rho+mp.mpf('.1')))
    M=raw(t,0)
    mu=[mp.mpf(1)]+[raw(t,j)/M for j in range(1,6)]
    kap=[mp.mpf(0)]*6
    for j in range(1,6):
        kap[j]=mu[j]-sum(mp.binomial(j-1,a-1)*kap[a]*mu[j-a] for a in range(1,j))
    sigma=mp.sqrt(kap[2]); lam={j:kap[j]/sigma**j for j in range(3,6)}
    u=abs(t)*sigma*mp.sqrt(k); eps=1 if t>=0 else -1; eta=1/mp.sqrt(k)
    A=k*mp.log(M)-t*m
    def herm(d,z):
        return sum((-1)**q*mp.factorial(d)/(2**q*mp.factorial(q)*mp.factorial(d-2*q))*z**(d-2*q) for q in range(d//2+1))
    def H(d):
        return mp.quad(lambda z:mp.exp(-u*z-z*z/2)*herm(d,z)/mp.sqrt(2*mp.pi),[0,mp.inf])
    B=H(0)
    if R>=1:B+=eta*lam[3]*eps*H(3)/6
    if R>=2:B+=eta**2*(lam[4]*H(4)/24+lam[3]**2*H(6)/72)
    if R>=3:B+=eta**3*eps*(lam[5]*H(5)/120+lam[3]*lam[4]*H(7)/144+lam[3]**3*H(9)/1296)
    T=mp.exp(A)*B
    return (1-T if eps==1 else T),t,u

rows=[]
for m,k in [(10,5),(10,10),(10,11),(10,20),(20,10),(20,20),(20,21),(20,40),(40,20),(40,24),(40,34),(40,40),(40,41),(40,46),(40,56),(40,80)]:
    frac=exact_success(m,k); p=mp.mpf(frac.numerator)/frac.denominator
    row={'m':m,'k':k,'p_exact':mp.nstr(p,24)}
    for R in [0,1,3]:
        approx,t,u=saddle_approx(m,k,R)
        rel=abs(approx-p)/min(p,1-p)
        row[f'relative_smaller_tail_error_R{R}']=mp.nstr(rel,12)
        row[f'scaled_error_R{R}']=mp.nstr(rel*k**mp.mpf((R+1)/2),12)
    row['t']=mp.nstr(t,20);row['u']=mp.nstr(u,20)
    print(row,flush=True);rows.append(row)
Path(__file__).with_name('checks.json').write_text(json.dumps({'symbolic_checks':'PASS: P1 and c1','numerics':rows},indent=2)+'\n')
