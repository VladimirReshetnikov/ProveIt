"""Subtracted-integral checks at positive Stieltjes index.

The left side uses local singular terms only; the right side uses the
undilated closed forms plus the newly derived dilation formula.
"""
from fractions import Fraction
from math import gcd
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps=28

def M(x):
    if isinstance(x,Fraction):
        return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(x)

def g(n,x):
    return -mp.digamma(x) if n==0 else mp.stieltjes(n,x)

def gd(n,r,x):
    if n==0:
        return -mp.polygamma(r,x)
    assert n==1
    H=sum(mp.mpf(1)/j for j in range(1,r+1))
    return (-1)**(r+1)*mp.factorial(r)*(mp.diff(lambda s:mp.zeta(s,x),r+1)+H*mp.zeta(r+1,x))

def direct(p,q,m,n,a):
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
        alpha=M((p*x0)%1)
        beta=M((q*x0+a)%1)
        if sites[x0]=='first':
            scale=p
            other=q
            singidx=m
            smoothidx=n
            location=beta
        else:
            scale=q
            other=p
            singidx=n
            smoothidx=m
            location=alpha
        atstart=g(smoothidx,location)
        derivatives=[gd(smoothidx,j,location)*other**j/mp.factorial(j) for j in range(1,5)]
        def integrand(t):
            if not t:
                return mp.mpf(0)  # immaterial isolated endpoint
            if t<mp.mpf('1e-8'):
                diff=sum(c*t**j for j,c in enumerate(derivatives,1))
                smooth=atstart+diff
            else:
                smooth=g(smoothidx,location+other*t)
                diff=smooth-atstart
            regular=g(singidx,1+scale*t)*smooth
            return regular+mp.log(scale*t)**singidx/(scale*t)*diff
        integral=mp.quad(integrand,[0,ell/4,ell])
        primitive=atstart/(scale*(singidx+1))*(mp.log(scale*ell)**(singidx+1)-mp.log(scale)**(singidx+1))
        total+=integral+primitive
    return total

def I(m,n,t):
    b=1-t
    if (m,n)==(0,0):
        return g(1,t)+g(1,b)-2*mp.zeta(2)
    if (m,n)==(1,0):
        return g(2,t)/2+g(2,b)+mp.zeta(2)*(g(0,t)+g(0,b))-mp.zeta(3)
    if (m,n)==(0,1):
        return I(1,0,b)
    if (m,n)==(1,1):
        return (g(3,t)+g(3,b))/2+2*mp.zeta(2)*(g(1,t)+g(1,b))+mp.zeta(3)*(g(0,t)+g(0,b))-mp.zeta(2)**2-mp.zeta(4)
    raise NotImplementedError

def trace(n,M,x):
    L=mp.log(M)
    return sum(mp.binomial(n,j)*(-L)**(n-j)*g(j,x) for j in range(n+1))-(-L)**(n+1)/(n+1)

def expected(p,q,m,n,a):
    d=gcd(p,q)
    P,Q=p//d,q//d
    t=M((P*Fraction(a))%1)
    A,B,Lp,Lq=mp.log(P),mp.log(Q),mp.log(p),mp.log(q)
    mix=sum(mp.binomial(m,i)*mp.binomial(n,j)*(-B)**(m-i)*(-A)**(n-j)*I(i,j,t) for i in range(m+1) for j in range(n+1))
    return (mix+(((-B)**(m+1)-Lp**(m+1))/(m+1))*trace(n,P,t)+(((-A)**(n+1)-Lq**(n+1))/(n+1))*trace(m,Q,1-t)+(-B)**(m+1)*(-A)**(n+1)/((m+1)*(n+1)))

if __name__=='__main__':
    tests=[(2,1,1,0,'1/7'),(2,1,0,1,'1/7'),(2,3,1,1,'1/7')]
    rows=[]
    for p,q,m,n,a in tests:
        lhs=direct(p,q,m,n,a)
        rhs=expected(p,q,m,n,a)
        error=abs(lhs-rhs)
        scale=max(1,abs(rhs))
        row={'p':p,'q':q,'m':m,'n':n,'a':a,'integral':mp.nstr(lhs,26),'formula':mp.nstr(rhs,26),'absolute_error':mp.nstr(error,6),'relative_error':mp.nstr(error/scale,6),'passed':error/scale<mp.mpf('1e-23')}
        rows.append(row)
        print(json.dumps(row),flush=True)
    (Path(__file__).resolve().parents[1] / 'results' / 'dilated_stieltjes.json').write_text(json.dumps({'working_precision':mp.mp.dps,'tests':rows},indent=2)+'\n')
    assert all(x['passed'] for x in rows)
