#!/usr/bin/env python3
"""Independent integer Wick recursion checks against graph polynomials.
This verifier does not fit or extrapolate any asymptotic coefficient.
"""
from functools import lru_cache
from fractions import Fraction as F
from derive_second_correction import cumulant_polynomial, eval_poly, asymptotic, alpha, require, simplify_polynomial, COV46_FORMULA, CUM444_FORMULA

def wick(degrees,cov):
    @lru_cache(None)
    def m(ds):
        if not any(ds): return 1
        i=next(i for i,d in enumerate(ds) if d)
        rest=list(ds); rest[i]-=1
        ans=0
        for j,d in enumerate(rest):
            if d:
                sub=rest.copy(); sub[j]-=1
                ans+=d*cov[i][j]*m(tuple(sub))
        return ans
    return m(tuple(degrees))

def projector_numerators(n):
    w=[i-(n+1)//2 if n%2 else 2*i-n-1 for i in range(1,n+1)]
    S=sum(x*x for x in w)
    cells=[(i,j) for i in range(n) for j in range(n)]
    P=[[S*((w[j]*w[l] if i==k else 0)+(w[i]*w[k] if j==l else 0))-w[i]*w[j]*w[k]*w[l] for k,l in cells] for i,j in cells]
    return S,P

def direct_cov46(S,P):
    total=0
    for i in range(len(P)):
        for j in range(len(P)):
            h,k,p=P[i][i],P[j][j],P[i][j]
            total+=wick((4,6),((h,p),(p,k)))-3*h*h*15*k**3
    return F(total,12*45*S**10)

def direct_cum444(S,P):
    total=0
    for i in range(len(P)):
      for j in range(len(P)):
       for k in range(len(P)):
        a,b,c=P[i][i],P[j][j],P[k][k]
        p,q,r=P[i][j],P[i][k],P[j][k]
        mu=(3*a*a,3*b*b,3*c*c)
        raw=wick((4,4,4),((a,p,q),(p,b,r),(q,r,c)))
        raw-=mu[0]*wick((4,4),((b,r),(r,c)))
        raw-=mu[1]*wick((4,4),((a,q),(q,c)))
        raw-=mu[2]*wick((4,4),((a,p),(p,b)))
        raw+=2*mu[0]*mu[1]*mu[2]
        total+=raw
    return F(total,12**3*S**12)

def verify():
    p46,_=cumulant_polynomial([4,6],F(1,12*45))
    p444,_=cumulant_polynomial([4,4,4],F(1,12**3))
    require(simplify_polynomial(p46)==COV46_FORMULA, "transcribed exact covariance formula mismatch")
    require(simplify_polynomial(p444)==CUM444_FORMULA, "transcribed exact third cumulant formula mismatch")
    results=[]
    for n in range(2,6):
        S,P=projector_numerators(n)
        w=[i-(n+1)//2 if n%2 else 2*i-n-1 for i in range(1,n+1)]
        a=[F(t*t,S) for t in w]
        x,y,z=(sum(t**k for t in a) for k in (2,3,4))
        h=[F(P[i][i],S*S) for i in range(len(P))]
        m=(2*n*x+2-4*x+x*x)/4
        H3=2*n*y+6*x-6*y-6*x*x+6*x*y-y*y
        H4=2*n*z+8*y+6*x*x-8*z-24*x*y+12*x*z+12*y*y-8*y*z+z*z
        A=6*x+(2*n-12)*x*x+6*x**3+x**4-4*x*x*y+2*y*y
        B=(2*n-2)*x*x+12*x**3+x**4+8*y-24*x*y-8*x*x*y+12*y*y
        require(m==sum(t*t for t in h)/4, f'quartic mean mismatch at n={n}')
        require(H3==sum(t**3 for t in h), f'H3 mismatch at n={n}')
        require(H4==sum(t**4 for t in h), f'H4 mismatch at n={n}')
        varnum=0
        for i in range(len(P)):
            for j in range(len(P)):
                hi,hj,pij=P[i][i],P[j][j],P[i][j]
                varnum+=wick((4,4),((hi,pij),(pij,hj)))-9*hi*hi*hj*hj
        require(F(varnum,144*S**8)==A/2+B/6, f'quartic variance mismatch at n={n}')
        cov=direct_cov46(S,P)
        third=direct_cum444(S,P)
        require(cov==eval_poly(p46,n), f'covariance mismatch at n={n}')
        require(third==eval_poly(p444,n), f'third cumulant mismatch at n={n}')
        results.append({'n':n,'cov_Q4_Q6':str(cov),'cum3_Q4':str(third),'passed':True})
    d2=F(10,3)*alpha(2)*alpha(3)+4*alpha(3)+F(34,3)*alpha(2)**2
    t2=11*alpha(2)**3+2*alpha(3)+37*alpha(2)**2
    require(d2==asymptotic(p46,-2)==F(13176,175), "covariance leading coefficient mismatch")
    require(t2==asymptotic(p444,-2)==F(167778,875), "third cumulant leading coefficient mismatch")
    L2=F(39,100)-F(2691,350)+F(2484,175)-F(8466,175)+d2-t2/6
    c2=L2+F(171,350)**2/2
    require(L2==F(6483,3500), "log coefficient mismatch")
    require(c2==F(483051,245000), "second coefficient mismatch")
    result={'method':'Independent raw integer Wick recurrence for small-n checks; finite symbolic graph identities for asymptotic proof','all_passed':True,'checks':results,'logarithmic_second_coefficient':str(L2),'c2':str(c2)}
    return result

