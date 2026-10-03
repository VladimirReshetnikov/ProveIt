#!/usr/bin/env python3
"""Exact finite tests of the conjectural rational collapse (NOT a proof in h).

Requires SymPy. Tests polynomial identities for h=4,...,16 using a common
falling-factorial denominator, independently of asymptotic interpolation.
"""
import sympy as S
from math import factorial,comb
from fractions import Fraction as Q
from path_forests import partitions as parts, rising
import time,json
n=S.Symbol('n')

def polyprod(start,length):
 p=S.Poly(1,n,domain=S.QQ)
 for a in range(start,start+length):p*=S.Poly(n-a,n,domain=S.QQ)
 return p

def profile(partition):
 b=[0]*max(partition,default=0)
 for a in partition:b[a-1]+=1
 return tuple(b)

def FF(b):
 c=sum(b);k=sum((i+1)*v for i,v in enumerate(b))
 E=[1]+[0]*c
 for i,count in enumerate(b,1):
  for _ in range(count):
   for h in range(c,0,-1): E[h]+=i*E[h-1]
 out=S.Poly(0,n,domain=S.QQ)
 for h in range(c+1):
  out+=((-1)**h*factorial(h)*E[h])*polyprod(k+h,c-h)
 return out

def check(H):
 out=S.Poly(0,n,domain=S.QQ)
 for k in range(H+1):
  for p in parts(k):
   b=profile(p);c=sum(b);v=k+c
   den=factorial(H-k)
   for z in b:den*=factorial(z)
   out+=S.Rational((-1)**(H-k),den)*FF(b)**2*polyprod(v,2*H-v)
 target=24*polyprod(H-1,H-4)
 return (out-target).is_zero

if __name__=='__main__':
 start=time.time()
 for H in range(4,17):
  ok=check(H);print(H,ok,'seconds',time.time()-start,flush=True)
  assert ok
