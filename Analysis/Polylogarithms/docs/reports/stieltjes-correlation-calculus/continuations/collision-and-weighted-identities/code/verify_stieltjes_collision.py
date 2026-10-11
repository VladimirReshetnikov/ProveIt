"""Positive-Stieltjes-index checks by explicit real local subtraction.

This uses no spectral correlation identity on the left.  A high-order
Taylor polynomial is used only below t=1e-7 to avoid cancellation.
Its first omitted contribution is below t**10 times a smooth coefficient.
The computations are floating-point consistency checks, not enclosures.
"""
from fractions import Fraction
from math import gcd
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps=36


def gd(m,r,x):
    if m==0:
        return -mp.digamma(x) if r==0 else -mp.polygamma(r,x)
    assert m==1
    if r==0:
        return mp.stieltjes(1,x)
    return ((-1)**(r+1)*mp.factorial(r)*
            (mp.diff(lambda s:mp.zeta(s,x),r+1)+mp.harmonic(r)*mp.zeta(r+1,x)))


def frac_mpf(x):
    return mp.mpf(x.numerator)/x.denominator


def prim(poly, exponent, ell):
    # Coefficients of the polynomial are in ascending powers of log(t).
    if exponent==-1:
        return sum(c*mp.log(ell)**(j+1)/(j+1) for j,c in enumerate(poly))
    a=mp.mpf(exponent+1)
    total=mp.mpf(0)
    for j,c in enumerate(poly):
        value=sum((-1)**h*mp.factorial(j)/mp.factorial(j-h)*
                  mp.log(ell)**(j-h)/a**(h+1) for h in range(j+1))
        total+=c*ell**a*value
    return total


def poly_product(a,b):
    c=[mp.mpf(0)]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        for j,bj in enumerate(b):
            c[i+j]+=ai*bj
    return c


def fp_integral(p,q,m,n,r,k):
    points=sorted({Fraction(j,p) for j in range(p+1)}|
                  {Fraction(j,q) for j in range(q+1)})
    total=mp.mpf(0)
    for left,right in zip(points,points[1:]):
        ell=frac_mpf(right-left)
        ap,aq=(p*left)%1,(q*left)%1
        sp,sq=ap==0,aq==0
        ap=mp.mpf(1) if sp else frac_mpf(ap)
        aq=mp.mpf(1) if sq else frac_mpf(aq)
        cp=(-1)**r*mp.factorial(r)/mp.mpf(p)**(r+1)
        cq=(-1)**k*mp.factorial(k)/mp.mpf(q)**(k+1)
        pp=[mp.log(p)-(mp.harmonic(r) if r else 0),mp.mpf(1)] if m else [mp.mpf(1)]
        pq=[mp.log(q)-(mp.harmonic(k) if k else 0),mp.mpf(1)] if n else [mp.mpf(1)]
        ca=[gd(m,r+j,ap)*mp.mpf(p)**j/mp.factorial(j) for j in range(k+11)] if sq else []
        cb=[gd(n,k+j,aq)*mp.mpf(q)**j/mp.factorial(j) for j in range(r+11)] if sp else []
        if sp and sq:
            total+=cp*cq*prim(poly_product(pp,pq),-r-k-2,ell)
        if sp:
            total+=sum(cp*cb[j]*prim(pp,j-r-1,ell) for j in range(r+1))
        if sq:
            total+=sum(cq*ca[j]*prim(pq,j-k-1,ell) for j in range(k+1))

        def tail(gm,gr,a,scale,order,coeff,t):
            if t<mp.mpf('1e-7'):
                return sum(coeff[j]*t**(j-order-1) for j in range(order+1,len(coeff)))
            return (gd(gm,gr,a+scale*t)-sum(coeff[j]*t**j for j in range(order+1)))/t**(order+1)

        def residual(t):
            if not t:
                return mp.mpf(0)
            ga,gb=gd(m,r,ap+p*t),gd(n,k,aq+q*t)
            value=ga*gb
            if sp:
                value+=cp*sum(c*mp.log(t)**j for j,c in enumerate(pp))*tail(n,k,aq,q,r,cb,t)
            if sq:
                value+=cq*sum(c*mp.log(t)**j for j,c in enumerate(pq))*tail(m,r,ap,p,k,ca,t)
            return value

        total+=mp.quad(residual,[0,ell/4,ell])
    return total


def closed(p,q,m,n):
    d=gcd(p,q)
    P,Q=p//d,q//d
    K=mp.log(p*q//d)
    z,dz,ddz=mp.zeta(2),mp.diff(mp.zeta,2),mp.diff(mp.zeta,2,2)
    if (m,n)==(1,0):
        return P*(ddz/2+K*dz+(K*K/2+mp.log(p)-1)*z)
    assert (m,n)==(0,1)
    return P*(-ddz/2-(K+1)*dz-(K*K/2+mp.log(P))*z)


if __name__=='__main__':
    rows=[]
    for p,q,m,n in [(2,3,1,0),(2,3,0,1)]:
        lhs=fp_integral(p,q,m,n,0,1)
        rhs=closed(p,q,m,n)
        residual=abs(lhs-rhs)/max(1,abs(rhs))
        row={'p':p,'q':q,'m':m,'n':n,'r':0,'k':1,
             'subtracted_integral':mp.nstr(lhs,33),'formula':mp.nstr(rhs,33),
             'relative_residual':mp.nstr(residual,6)}
        rows.append(row)
        print(json.dumps(row),flush=True)
        assert residual<mp.mpf('1e-25')
    (Path(__file__).resolve().parent.parent / 'results' / 'stieltjes_collision_validation.json').write_text(
        json.dumps({'precision_dps':mp.mp.dps,'checks':rows,
                    'status':'floating-point consistency, not certified intervals'},indent=2))
