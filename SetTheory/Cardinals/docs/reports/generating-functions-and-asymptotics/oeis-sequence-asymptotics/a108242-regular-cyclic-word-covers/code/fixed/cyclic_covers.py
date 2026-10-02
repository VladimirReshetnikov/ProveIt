"""Exact fixed-degree cyclic-cover sums and rational coefficient checks.
Run: python3 cyclic_covers.py. No external Python packages are required.
"""
from fractions import Fraction as F
from math import factorial as fac
from pathlib import Path
import json,re

def fall(n,k):return fac(n)//fac(n-k)
def exact(n,sign=1):
 z=F(0)
 for b in range(n//3+1):
  for c in range((n-3*b)//3+1):
   for d in range(n-3*b-3*c+1):
    k=3*b+3*c+d;a=n-2*b-3*c-d
    if a<0:continue
    z+=F(sign**b*fall(n,k)*fac(3*a)*2**d,6**(n-k)*3**(a+d)*fac(a)*6**b*fac(b)*9**c*fac(c)*fac(d))
 assert z.denominator==1
 return z.numerator

def exact_degree2(m,sign):
 n=3*m;z=F(0)
 for b in range(m+1):
  a=2*m-2*b;k=3*b
  z+=F(sign**b*fall(n,k)*fac(3*a),2**(n-k)*3**a*fac(a)*6**b*fac(b))
 assert z.denominator==1
 return z.numerator

def conv(a,b,M):
 c=[F(0)]*(M+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b[:M+1-i]):c[i+j]+=x*y
 return c

def coeffs(M,sign):
 S=[F(0)]*(M+1)
 for b in range(M+1):
  for c in range((M-b)//3+1):
   for d in range(M-b-3*c+1):
    h=b+3*c+d;k=3*b+3*c+d;r=2*b+3*c+d;m=M-h
    C=F(sign**b*6**k*3**r*2**d,6**b*fac(b)*9**c*fac(c)*3**d*fac(d)*3**(3*r))
    a=[F(1)]+[F(0)]*m
    for v in list(range(k))+list(range(r)):a=conv(a,[F(1),F(-v)],m)
    for v in range(3*r):a=conv(a,[F(v,3)**j for j in range(m+1)],m)
    for j in range(m+1):S[h+j]+=C*a[j]
 return S

def oeis_values(id):
 t=Path(__file__).with_name(id+'.seq').read_text()
 return [int(x) for x in ','.join(re.findall(r'^%[STU] '+id+r' (.*)$',t,re.M)).split(',') if x]
if __name__=='__main__':
 checks={}
 for id,s in [('A108242',1),('A110105',-1)]:
  vals=oeis_values(id)
  assert all(exact(n,s)==v for n,v in enumerate(vals))
  checks[id]={'oeis_terms_checked':len(vals),'relative_to_configuration':[str(x) for x in coeffs(8,s)]}
 for id,s in [('A110106',1),('A110104',-1)]:
  vals=oeis_values(id)
  assert all(exact_degree2(n,s)==v for n,v in enumerate(vals))
  checks[id]={'oeis_terms_checked':len(vals)}
 Path(__file__).with_name('cyclic-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
 print(json.dumps(checks,indent=2))
