#!/usr/bin/env python3
"""Independent truncated rational algebra in h and P=pi^2. No symbolic library."""
import sys
if not __debug__: raise SystemExit('Assertions must be enabled; do not use -O.')
from fractions import Fraction as F
from pathlib import Path
import argparse,json,hashlib
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',default=str(Path(__file__).parent));ar=pa.parse_args();out=Path(ar.output_dir);out.mkdir(parents=True,exist_ok=True)
CUT=9
# Sparse Q[P][h]/(h^(CUT+1)); pairs denote exponents of h and P.
def mono(h=0,p=0,c=1):return {(h,p):F(c)} if c else {}
one=mono();h=mono(1);P=mono(0,1)
def add(*xs):
 o={}
 for x in xs:
  for k,v in x.items():o[k]=o.get(k,F(0))+v
 return {k:v for k,v in o.items() if v}
def scale(x,c):return {k:v*c for k,v in x.items() if v*c}
def mul(*xs):
 o=one
 for x in xs:
  t={}
  for (a,b),v in o.items():
   for (c,d),w in x.items():
    if a+c<=CUT:t[a+c,b+d]=t.get((a+c,b+d),F(0))+v*w
  o={k:v for k,v in t.items() if v}
 return o
def pw(x,n):
 o=one
 for _ in range(n):o=mul(o,x)
 return o
def inv(x):
 assert x.get((0,0),0)==1 and not any(a==0 and b for a,b in x)
 u=add(one,scale(x,-1));return add(*(pw(u,j) for j in range(CUT+1)))
def log(x):
 assert x.get((0,0),0)==1 and not any(a==0 and b for a,b in x)
 u=add(x,scale(one,-1));return add(*(scale(pw(u,j),F((-1)**(j+1),j)) for j in range(1,CUT+1)))
def deriv(x):return {(a-1,b):a*v for (a,b),v in x.items() if a}
def comp(x,v):return add(*(scale(mul(pw(v,a),mono(0,b)),c) for (a,b),c in x.items()))
def coeff(x,n):return {p:c for (a,p),c in x.items() if a==n}
def atdegree(poly,n):return {(n,p):c for p,c in poly.items() if c}
# Independent explicit inverse derivatives R1,R3,R5 and even Fermi moments.
r1=mul(h,inv(add(one,scale(h,-1))))
r3=mul(add(mono(4,c=2),mono(5)),pw(inv(add(one,scale(h,-1))),5))
r5=mul(add(mono(6,c=24),mono(7,c=58),mono(8,c=22),mono(9)),pw(inv(add(one,scale(h,-1))),9))
rr=r1
for j in range(1,5):
 rr=mul(r1,add(rr,scale(mul(h,deriv(rr)),-1)))
 if j==2: assert rr==r3
 if j==4: assert rr==r5
T=add(scale(mul(P,r1),F(1,6)),scale(mul(pw(P,2),r3),F(7,360)),scale(mul(pw(P,3),r5),F(31,15120)))
rho=one
for k in range(2,8):
 lr=log(rho);v=mul(h,inv(add(one,mul(h,lr))))
 saddle=add(scale(mul(add(one,scale(pw(inv(rho),2),-1)),add(one,mul(h,lr),scale(h,-1))),F(1,2)),mul(h,add(comp(T,v),scale(mul(pw(v,2),comp(deriv(T),v)),-1))))
 rho=add(rho,scale(atdegree(coeff(saddle,k),k),-1))
lr=log(rho);v=mul(h,inv(add(one,mul(h,lr))))
hQ=add(scale(mul(add(rho,inv(rho)),add(one,mul(h,lr))),F(1,2)),scale(mul(h,rho),-1),mul(h,rho,comp(T,v)))
d={j:coeff(hQ,j+1) for j in range(1,7)}
expected_d={1:{1:F(1,6)},2:{1:F(1,6)},3:{1:F(1,6),2:F(-1,72)},4:{1:F(1,6),2:F(1,40)},5:{1:F(1,6),2:F(41,180),3:F(1,432)},6:{1:F(1,6),2:F(3,4),3:F(1973,45360)}}
assert d==expected_d,(d,expected_d)
D=add(*(atdegree(c,j) for j,c in d.items()));tau=one
for k in range(2,8):
 lt=log(tau);v=mul(h,inv(add(one,mul(h,lt))))
 eq=add(mul(tau,add(one,mul(h,lt),scale(h,-1),mul(h,comp(D,v)))),scale(add(one,scale(h,-1)),-1))
 tau=add(tau,scale(atdegree(coeff(eq,k),k),-1))
b={j:coeff(pw(tau,2),j) for j in range(2,8)}
expected_b={2:{1:F(-1,3)},3:{1:F(-1,3)},4:{1:F(-1,3),2:F(1,9)},5:{1:F(-1,3),2:F(1,30)},6:{1:F(-1,3),2:F(-77,180),3:F(-1,27)},7:{1:F(-1,3),2:F(-19,12),3:F(-167,2835)}}
assert b==expected_b,(b,expected_b)
assert coeff(rho,2)=={1:F(-1,6)} and coeff(rho,3)=={1:F(-1,6)} and coeff(rho,4)=={2:F(1,24)}
def enc(x):return {str(k):{str(p):str(c) for p,c in sorted(v.items())} for k,v in x.items()}
r={'status':'PASS','scope':'Exact formal coefficient identities; analytic uniformity is separately proved.','log_coefficients':enc(d),'inverse_squared_ratio_coefficients':enc(b),'saddle_ratio_coefficients':enc({j:coeff(rho,j) for j in range(2,8)}),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(out/'log_hierarchy_verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
