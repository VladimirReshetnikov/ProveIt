#!/usr/bin/env python3
"""Finite symbolic Gaussian algorithms for both A113226 saddles.
All derivatives below are with respect to v=log u. No external input needed.
"""
import argparse,json
from pathlib import Path
import sympy as s

def gaussian(poly,x,var):
    ans=0
    for (k,),v in s.Poly(s.expand(poly),x).terms():
        if k%2==0: ans+=v*s.factorial2(k-1)*var**(k//2)
    return s.factor(ans)

def exponential(q,K):
    e=[s.Integer(1)]
    for k in range(1,K+1): e.append(s.expand(sum(j*q[j]*e[k-j] for j in range(1,k+1))/k))
    return e

def first_saddle(J):
    c,x=s.symbols('c x',positive=True); g=s.symbols('g1:'+str(J+1));K=2*J
    q=[s.Integer(0)]*(K+1)
    def add(a,b,p):
        for k in range(K-b+1):q[b+k]+=a*s.binomial(p,k)*(s.I*x)**k
    for k in range(3,K+3):q[k-2]+=2*c*s.binomial(-s.Rational(1,2),k)*(s.I*x)**k
    for m in range(2,(K+6)//4+1):
        if 4*m-6<=K:add(c**m/s.Integer(m),4*m-6,m)
    for m in range(1,K//4+1):add(c**m/s.Integer(m),4*m,m)
    for j in range(1,J+1):add(g[j-1]*c**s.Rational(j,2),2*j,s.Rational(j,2))
    e=exponential(q,K)
    return c,g,[gaussian(e[2*j],x,2/(3*c)) for j in range(J+1)]

def second_saddle(J):
    # h=n^(-1/6), theta=h^3 x; delta=h^2.
    x,V=s.symbols('x V',positive=True); K=2*J
    cs=s.symbols('C1:'+str(K+1)); fs=s.symbols('F3:'+str(K+7));ds=s.symbols('D1:'+str(K+1))
    q=[s.Integer(0)]*(K+1)
    for m in range(3,(K+6)//3+1):q[3*m-6]+=fs[m-3]*(s.I*x)**m/s.factorial(m)
    for m in range(1,(K+2)//3+1):q[3*m-2]+=3*cs[m-1]*(s.I*x)**m/s.factorial(m)
    for m in range(1,K//3+1):q[3*m]+=ds[m-1]*(s.I*x)**m/s.factorial(m)
    e=exponential(q,K)
    # a_j(v+i theta), with a_0=1. A{j}_{m} denotes m-th derivative of a_j.
    amp=[s.Integer(0)]*(K+1);amp[0]=1
    for j in range(1,J+1):
        for m in range((K-2*j)//3+1):amp[2*j+3*m]+=s.Symbol(f'A{j}_{m}')*(s.I*x)**m/s.factorial(m)
    out=[]
    for j in range(J+1):out.append(gaussian(sum(amp[k]*e[2*j-k] for k in range(2*j+1)),x,1/V))
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--order',type=int,default=3);a=p.parse_args()
    c,g,co=first_saddle(a.order);b=second_saddle(a.order)
    out={'order':a.order,'first_saddle':[str(x) for x in co],'second_saddle':[str(x) for x in b], 'second_notation':'C_m=c^(m)(v), F_m=f^(m)(v), D_m=d^(m)(v), A_j_m=a_j^(m)(v), V=f_second(v); derivatives in v=log u'}
    Path(__file__).with_name('refined_coefficients.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
