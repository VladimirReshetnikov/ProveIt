#!/usr/bin/env python3
"""Bounded arithmetic controls for the new unbounded lemmas in the report."""
from itertools import product
from math import comb,factorial,gcd
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def pell(a,n):
    x,y=1,0
    for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def check():
    separation=canonical=crt=0
    for W in range(4,10):
        A=W**3+2
        for H in range(2,W):
            cap=pell(A,H)[1]
            for indices in product(range(H),repeat=2):
                ys=[pell(A,k)[1] for k in indices]
                require(cap-H-1-sum(ys)>=0,'cap completeness slack')
                require(sum((y-k)**2 for y,k in zip(ys,indices))%(A-1)==0,
                        'canonical pooled congruence')
                canonical+=1
            for js in product(range(H),repeat=2):
                for ks in product(range(W),repeat=2):
                    E=sum((j-k)**2 for j,k in zip(js,ks))
                    require(E<A-1,'strict small-error bound')
                    require((E%(A-1)==0)==(js==ks),'pooled separation')
                    separation+=1
    for t in range(2,8):
        F=factorial(t);d=[1+F*F//i for i in range(1,t+1)]
        require(all(gcd(a,b)==1 for i,a in enumerate(d) for b in d[i+1:]),'CRT coprimality')
        B=1
        for v in d:B*=v
        require(B==comb(F*F+t,t),'reciprocal binomial product')
        for K in (2,3,4):
            N=B**K;period=N*N
            require(period==__import__('math').prod(v**(2*K) for v in d),'exact CRT period')
            for a,b in ((1,1),(period,1),(period//2,period)):
                I=lambda u,v:2*(u+v)*(u+v+1)+4*v
                shifted=a+period
                require(I(shifted,b)>2*N**4,'semantic anchor lower bound')
                require((I(shifted,b)-I(a,b))%period==0,'lift preserves constructor congruence')
                require(shifted+8*period<=10*period,'nine-representative budget')
                crt+=1
    n,k,m,W,A=2,24,1,29,2**22+1
    T=2*A*n-n*n-1
    X,Y=pell(A,k);residue=X+(n-A)*Y
    require(A-1>W**3 and T==2**24-1,'counterexample hypotheses')
    require(n**k!=m and residue>=m and (residue-m)%T==0,'false power counterexample')
    return {'verified':True,'pooled_error_separations':separation,
            'canonical_cap_extensions':canonical,'CRT_lift_controls':crt,
            'insufficient_growth_counterexample':{'n':n,'k':k,'m':m,'W':W,'A':A,'T':T},
            'scope':'finite arithmetic controls; unbounded proofs are in report.tex'}


if __name__=='__main__':print(json.dumps(check(),indent=2))
