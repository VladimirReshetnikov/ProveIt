#!/usr/bin/env python3
"""Exact formal inverse coefficients for A124380; no network access.
Usage: python replay_inverse.py --order 4
n(y) = 2 X^2 + sum(b_j(L)*X^(1-j),j=0..order),
X=sqrt(y/W(y/e)), L=log(X). Symbol c means 1/2-log(2).
"""
import argparse, json
from functools import lru_cache
import sympy as s
from replay_coefficients import coefficients

def inverse_coefficients(order):
    L, _, _, P = coefficients(max(0,order-1))
    c=s.Symbol('c')
    F={2:2*L-1,1:L+1,0:L*L/8+L+c}
    F.update({-j:P[j] for j in range(1,order)})
    d=[]
    def delta_power_coefficient(r,degree):
        if degree<0:return s.Integer(0)
        a=[s.Integer(1)]+[s.Integer(0)]*degree
        for _ in range(r):
            a=[s.expand(sum(a[v]*d[j-v] for v in range(j+1) if 0<=j-v<len(d))) for j in range(degree+1)]
        return a[degree]
    @lru_cache(None)
    def derivative_factor(p,r):
        if r==0:return F[p]
        prev=derivative_factor(p,r-1)
        return s.expand((p-r+1)*prev+s.diff(prev,L))
    for k in range(order+1):
        m=k-1
        residual=s.Integer(0)
        for p in F:
            for r in range(max(0,m+p)+1):
                if p==2 and r==0:continue
                deg=m+p-r
                residual+=derivative_factor(p,r)*delta_power_coefficient(r,deg)/s.factorial(r)
        d.append(s.factor(-residual/(4*L)))
    b=[s.factor(4*d[j]+2*sum(d[i]*d[j-1-i] for i in range(j))) for j in range(order+1)]
    return L,c,d,b

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=4)
    parser.add_argument('--latex',action='store_true')
    args=parser.parse_args()
    if args.order<0:parser.error('order must be nonnegative')
    L,c,d,b=inverse_coefficients(args.order)
    if args.latex:
        for j,v in enumerate(b):print('b_'+str(j)+' = '+s.latex(v))
    else:
        print(json.dumps({'parameter':'X=sqrt(y/W(y/e)), L=log(X), c=1/2-log(2)',
            'x_coefficients':[str(v) for v in d],
            'n_coefficients':[str(v) for v in b],
            'meaning':'x=X+sum(d_j/X^j); n=2X^2+sum(b_j*X^(1-j))',
            'fixed_order_remainder_for_order_M_ge_2':'O_M((1+L)^(3*M-1)/X^M)',
            'sympy_version':s.__version__},indent=2))
if __name__=='__main__':main()
