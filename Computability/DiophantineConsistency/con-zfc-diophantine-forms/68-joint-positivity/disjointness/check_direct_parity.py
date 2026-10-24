#!/usr/bin/env python3
"""Independent finite checks, not a formal certificate or exhaustive theorem proof."""
from fractions import Fraction as F
from math import comb
import json

def psi(a,n):
    p,q=0,1
    for _ in range(n):p,q=q,2*a*q-p
    return p

cnt=0
for S in range(1,13):
 for T in range(1,13):
    n=S+T;e=2*n+4;d=e+2
    z=psi(e+3,d)
    assert z%d==0
    y=z//d-1;x=2*(y+1)
    assert x>128*2**n
    # x-coordinate of Pell can be obtained from neighboring y coordinates.
    u0=psi(e+3,d+1)-(e+3)*z
    assert u0*u0==(e+2)**3*(e+4)*(y+1)**2+1
    num=(x+1)**n;den=x**S;Q,rem=divmod(num,den)
    assert Q%2==comb(n,S)%2==int((S&T)==0)
    assert F(rem,den)<F(1,128)
    Y=Q if Q%2 else Q+1
    M=128*(n+1)*(x+1)*(Y+1);A=M*(x+1)
    C=psi(A,n+1);K=psi(M,T+1);L=psi(M*x,S+1)
    assert (K-T-1)%(M-1)==0 and (L-S-1)%(M*x-1)==0
    rho=F(num,den);sigma=F(C,K*L);eps=F(n,2*M)
    assert abs(rho-sigma)<=sigma*eps/(1-eps)
    assert abs(rho-sigma)<F(1,128)
    assert (abs(sigma-Y)<F(1,8)) == ((S&T)==0)
    assert M-1>=2*n+1 and (2*M-1)**2>2*A
    cnt+=1
print(json.dumps({'input_pairs':cnt,'checks':'growth-square construction, growth bound, parity, rank congruences, ratio estimate, odd-quotient acceptance','status':'pass'},indent=2))
