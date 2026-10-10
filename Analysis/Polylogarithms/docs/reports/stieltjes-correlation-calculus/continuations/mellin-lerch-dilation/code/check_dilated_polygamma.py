"""Independent convergent-integral checks for unequal dilation formulas.

All singular terms are removed from the pointwise integrand, using the
local Laurent series of polygamma. No Fourier or distribution formula
is used on the left-hand side.
"""
from fractions import Fraction
from math import gcd
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 42

def M(x):
    if isinstance(x, Fraction):
        return mp.mpf(x.numerator) / x.denominator
    return mp.mpf(x)

def psi(r, x):
    return mp.polygamma(r, x)

def subtracted_fp(p,q,r,k,a):
    a=Fraction(a)
    a_sites={Fraction(j,p):'first' for j in range(p)}
    b_sites={((Fraction(j)-a)/q)%1:'second' for j in range(q)}
    assert not(set(a_sites)&set(b_sites))
    sites={**a_sites,**b_sites}
    nodes=sorted(sites)
    total=mp.mpf(0)
    for idx,x0 in enumerate(nodes):
        end=nodes[idx+1] if idx+1<len(nodes) else Fraction(1)
        ell=M(end-x0)
        mid=(x0+end)/2
        f1=(p*mid).__floor__()
        f2=(q*mid+a).__floor__()
        alpha=M(p*x0-f1)
        beta=M(q*x0+a-f2)
        if sites[x0]=='first':
            order=r
            coeff=[(-1)**(r+1)*mp.factorial(r)*q**j/(p**(r+1)*mp.factorial(j))*psi(k+j,beta) for j in range(r+1)]
            at0=((-1)**(r+1)*q**(r+1)/(mp.mpf(p)**(r+1)*(r+1))*psi(k+r+1,beta)+psi(r,1)*psi(k,beta))
        else:
            order=k
            coeff=[(-1)**(k+1)*mp.factorial(k)*p**j/(q**(k+1)*mp.factorial(j))*psi(r+j,alpha) for j in range(k+1)]
            at0=((-1)**(k+1)*p**(k+1)/(mp.mpf(q)**(k+1)*(k+1))*psi(r+k+1,alpha)+psi(k,1)*psi(r,alpha))
        def integrand(t):
            if not t:
                return at0
            with mp.workdps(mp.mp.dps+40):
                value=psi(r,alpha+p*t)*psi(k,beta+q*t)
                value-=sum(c*t**(j-order-1) for j,c in enumerate(coeff))
            return +value
        integral=mp.quad(integrand,[0,ell],method='gauss-legendre',maxdegree=7)
        primitive=sum(c*(mp.log(ell) if j==order else ell**(j-order)/(j-order)) for j,c in enumerate(coeff))
        total+=integral+primitive
    return total

def expected(p,q,r,k,a):
    d=gcd(p,q)
    P,Q=p//d,q//d
    theta=M((P*Fraction(a))%1)
    b=1-theta
    L=mp.log(p*q//d)
    N=r+k
    if N==0:
        return (mp.stieltjes(1,theta)+mp.stieltjes(1,b)+L*(mp.digamma(theta)+mp.digamma(b))-mp.pi**2/3-L**2+mp.log(p)*mp.log(q))
    H=lambda n:sum(mp.mpf(1)/j for j in range(1,n+1))
    Z1=lambda x:mp.diff(lambda s:mp.zeta(s,x),N+1)
    return mp.factorial(N)*P**k*Q**r*((-1)**(k+1)*(Z1(theta)+(H(N)-H(r)+L)*mp.zeta(N+1,theta))+(-1)**(r+1)*(Z1(b)+(H(N)-H(k)+L)*mp.zeta(N+1,b)))

if __name__=='__main__':
    tests=[(1,1,0,0,'1/3'),(2,1,0,0,'1/7'),(2,3,0,0,'1/7'),(4,6,0,0,'1/7'),(2,3,0,1,'1/7'),(2,3,1,0,'1/7'),(2,3,1,1,'1/7'),(4,6,2,1,'1/7'),(3,2,1,2,'2/7')]
    rows=[]
    for p,q,r,k,a in tests:
        lhs=subtracted_fp(p,q,r,k,a)
        rhs=expected(p,q,r,k,a)
        error=abs(lhs-rhs)
        scale=max(1,abs(rhs))
        row={'p':p,'q':q,'r':r,'k':k,'a':a,'integral':mp.nstr(lhs,35),'formula':mp.nstr(rhs,35),'absolute_error':mp.nstr(error,6),'relative_error':mp.nstr(error/scale,6),'passed':error/scale<mp.mpf('1e-25')}
        rows.append(row)
        print(json.dumps(row),flush=True)
    (Path(__file__).resolve().parents[1] / 'results' / 'dilated_polygamma.json').write_text(json.dumps({'working_precision':mp.mp.dps,'tests':rows},indent=2)+'\n')
    assert all(x['passed'] for x in rows)
