#!/usr/bin/env python3
"""Independent finite diagnostics. No author module is imported. Not a proof."""
import json, math, hashlib
from pathlib import Path
from itertools import product
out={}
# Exact special-function product, pairwise coprimality and all small prime factors.
cases=0
for H in range(2,10):
 for n in range(1,H):
  T=math.factorial(H); Q=(4*T*n)**n+1; M=4*T*Q+1
  ms=[4*T*(i+1)-1 for i in range(n)]
  value=(4*T)**n*math.factorial(n)*math.comb(Q+n,n)%M
  assert value==math.prod(ms) and 0<value<Q<M
  assert all(math.gcd(a,b)==1 for a,b in __import__('itertools').combinations(ms,2))
  assert all(math.gcd(a,T)==1 and a%4==3 for a in ms)
  cases+=1
out['exact_product_cases']=cases
# Independent CRT assembly; composite binomial denominator invertibility included.
def crt(rs,ms):
 modulus=math.prod(ms)
 return sum(r*(modulus//m)*pow(modulus//m,-1,m) for r,m in zip(rs,ms))%modulus
U=2; n=3; H=8; T=math.factorial(H); ms=[4*T*(i+1)-1 for i in range(n)]
c=crt(list(range(n)),ms)
# local polynomial w-i=0
A=crt(list(range(n)),ms)
assert all((c-i)%mi==0 and (A-i)%mi==0 for i,mi in enumerate(ms))
assert math.gcd(math.factorial(U+1),math.prod(ms))==1
assert math.comb(A,U+1)%math.prod(ms)==0
# Nested norm leaves: range, local polynomial, index.
z=(math.comb(A,U+1),A-c,4*T*(c+1)-1)
assert (z[0]**2+(z[1]**2+z[2]**2)**2)%math.prod(ms)==0
out['composite_crt_fixture']=True
# Anisotropy and range extraction independently over small inert primes.
count=0
for p in (3,7,11,19,23,31):
 for a,b in product(range(p),repeat=2):
  assert ((a*a+b*b)%p==0)==(a==b==0)
  count+=1
 for U in range(p-1):
  for A in range(3*p):
   assert (math.comb(A,U+1)%p==0)==(A%p<=U)
out['anisotropy_pairs']=count
out['binomial_range_verified']=True
# Boundary bijection for arbitrary signed alpha; retained guard is checked both ways.
boundary=0
for B in range(2,6):
 for m in range(1,4):
  M=B**m
  for D in range(B**(m-1),M):
   for C in range(3*M):
    ds=tuple(C//B**i%B for i in range(m))
    fixed=tuple(D//B**i%B for i in range(m))
    assert ((C-D)%M==0)==(ds==fixed)
    if (C-D)%M==0:
     V=(C-D)//M
     assert V>=0
     for q,F in ((1,0),(5,2),(100,3)):
      alpha=q-F-C
      assert alpha==q-F-D-M*V
      assert (F*alpha>0)==(F*(q-F-D-M*V)>0)
    boundary+=1
out['boundary_cases']=boundary
# Counterexample to omitting positive-domain restriction after substitution.
q,F,D,M,V=2,1,1,2,1
assert V>0 and q-F-D-M*V<0
out['positive_domain_negative_control']=True
# Counterexample to flat sum-of-three-squares.
assert (1+1+1)%3==0
out['flat_norm_negative_control']=True
# Translated Boolean controller, independent subset DP rather than author's solver.
cover=0
for lam,B in ((3,2),(5,2),(7,2)):
 for n in (2,3):
  N=lam**n; T=N//lam; k=lam-1; C0=lam
  if T<=C0: continue
  assert {pow(B,k*j,N) for j in range(T)}=={1+C0*z for z in range(T)}
  for a in (1,3,5):
   positions=[a+k*j for j in range(T)]+[a+1]
   assert len(set(positions))==len(positions)
   reached={0}
   for pos in positions:
    v=pow(B,pos,N); reached|={(r+v)%N for r in tuple(reached)}
   assert reached==set(range(N)); cover+=1
out['independent_subset_coverage_cases']=cover
out['scope']='Finite independent diagnostics only; universal proof reviewed in AUDIT.md.'
here=Path(__file__).resolve().parent
(here/'CHECK_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,sort_keys=True))
