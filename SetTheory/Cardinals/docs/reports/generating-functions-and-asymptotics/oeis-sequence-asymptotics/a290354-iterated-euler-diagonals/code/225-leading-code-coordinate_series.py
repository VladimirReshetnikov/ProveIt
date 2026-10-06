#!/usr/bin/env python3
"""Exact formal Fatou coefficients; finite algebra only, not error bounds."""
import argparse
from fractions import Fraction as F
from math import factorial
import json

KNOWN=['-1/36','1/540','1/7776','-71/435456','8759/163296000',
       '31/20995200','-183311/16460236800','23721961/6207860736000',
       '293758693/117328567910400']

def multiply(a,b,N):
    out=[F(0)]*(N+1)
    for i,x in enumerate(a[:N+1]):
        for j,y in enumerate(b[:N-i+1]): out[i+j]+=x*y
    return out

def generate(order):
    if isinstance(order,bool) or not isinstance(order,int) or not 0<=order<=12:
        raise ValueError('formal order must be an integer from 0 to 12')
    N=order+2
    # g=(exp(w)-1)/w and its inverse, computed by triangular convolution.
    g=[F(1,factorial(k+1)) for k in range(N+1)]
    inverse=[F(1)]+[F(0)]*N
    for k in range(1,N+1): inverse[k]=-sum(g[j]*inverse[k-j] for j in range(1,k+1))
    gp=[F(k+1)*g[k+1] for k in range(N)]
    logder=multiply(gp,inverse,N-1)
    logg=[F(0)]+[logder[k-1]/k for k in range(1,N+1)]
    residual=[-2*inverse[k+1]+logg[k]/3 for k in range(N)]
    residual[0]-=1
    f=[F(0)]+g[:-1];power=[F(1)]+[F(0)]*N
    result=[]
    for j in range(1,order+1):
        power=multiply(power,f,N)
        coefficient=-residual[j+1]/F(j,2)
        result.append(coefficient)
        for k in range(N): residual[k]+=coefficient*(power[k]-(1 if k==j else 0))
    if any(residual[:order+2]): raise ArithmeticError('formal Abel residual did not vanish')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--order',type=int,default=9)
    args=ap.parse_args()
    try: values=generate(args.order)
    except ValueError as exc: ap.error(str(exc))
    print(json.dumps({'status':'exact formal coefficients only; no analytic remainder certificate',
                      'order':args.order,'coefficients':[str(x) for x in values]},indent=2))
