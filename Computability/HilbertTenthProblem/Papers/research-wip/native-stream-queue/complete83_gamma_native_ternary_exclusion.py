#!/usr/bin/env python3
"""Exact native ternary exclusion for the independent-gamma83 power tests."""
import argparse
import hashlib
import json
from math import comb, gcd
from pathlib import Path

PINS={
 'complete83_gamma_power_tests.py':'f3f73ad7c0ecf1c37097e9eab68c56dd5b0586408c56d05d458c6df49b514562',
 'complete83_gamma_power_tests.json':'07210a53139f13cb76ef3f05198cdf2ad2b391ed23aa29426babfe211cea2371',
 'complete83_gamma_power_tests.md':'4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete75_gamma87_compiler_order_filters.md':'43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3',
 'complete75_independent_gamma87_period.md':'dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117'}

def need(p,label):
 if not p:raise ValueError(label)
def sha(b):return hashlib.sha256(b).hexdigest()
def pairs(xs):
 out={}
 for k,v in xs:
  need(k not in out,'duplicate JSON key');out[k]=v
 return out
def loads(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda v:(_ for _ in ()).throw(ValueError(v)))
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def digits(n):
 need(type(n) is int and n>=0,'natural digit input');out=[]
 while n:out.append(n%3);n//=3
 return out or [0]
def val(n,p):
 need(n>0 and p>=2,'positive valuation input');v=0
 while n%p==0:n//=p;v+=1
 return v
def classify(r):
 ds=digits(r)
 need(r>0 and r%2==1 and ds[0]==0 and 2 not in ds,'ternary class hypotheses')
 s=sum(ds);z=sum(a*b for a,b in zip(ds,ds[1:]));b1=ds[1];e=(s+2*z)%6
 need(e in (1,3,5),'odd digit exponent')
 table={(0,1):15,(0,3):6,(0,5):24,(1,1):24,(1,3):15,(1,5):6}
 return dict(r=r,R=2*r+1,ternary=''.join(map(str,ds[::-1])),ones=s,adjacent_ones=z,next_digit=b1,exponent_mod6=e,a_mod27=table[b1,e],excludes_both_tests=(e==(3+2*b1)%6))
def native_direct(R,mod):
 r=(R-1)//2;X=pow(2,R,mod)
 G=sum(comb(2*r,r+j)*pow(X,j,mod) for j in range(r+1))%mod
 return (X+1)*G*pow(2,-1,mod)%mod

def native_prime_power(R,k):
 # Independently stream the whole row binom(R-1,j), retaining the 3-adic
 # valuation and its unit separately. No huge binomial integer is built.
 mod=3**k;r=(R-1)//2;x=pow(2,R,mod);xp=pow(x,-r,mod)
 unit=1;v=0;tail=0;terms=0
 for j in range(R):
  need(v>=0,'nonnegative binomial valuation')
  coefficient=0 if v>=k else unit*3**v%mod
  if j>=r:tail=(tail+coefficient*xp)%mod
  terms+=1
  if j<R-1:
   num=R-1-j;den=j+1
   while num%3==0:num//=3;v+=1
   while den%3==0:den//=3;v-=1
   unit=unit*(num%mod)*pow(den%mod,-1,mod)%mod
  xp=xp*x%mod
 return (x+1)*tail*pow(2,-1,mod)%mod,terms

def order2(H):
 z=2%H;n=1
 while z!=1:
  z=z*2%H;n+=1;need(n<=H,'order termination')
 return n

def verify(root):
 raw={}
 for name,h in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==h,'pin '+name);raw[name]=b
 gamma=loads(raw['complete83_independent_gamma_scout.json'])
 power_receipt=loads(raw['complete83_gamma_power_tests.json'])
 need(gamma['status']=='PASS' and power_receipt['status']=='PASS','parent receipts')
 # Formula for the central coefficient: exhaust every 0/1 ternary word
 # of at most seven digits, using exact integer binomial coefficients.
 central=[]
 for mask in range(128):
  r=sum(((mask>>i)&1)*3**i for i in range(7));ds=digits(r)
  s=sum(ds);z=sum(a*b for a,b in zip(ds,ds[1:]));got=comb(2*r,r)%9
  need(got==pow(2,s+2*z,9),'central digit formula')
  central.append(dict(r=r,central_mod9=got))
 # Direct small polynomial sums separately verify the two binomial identities.
 identity_cases=0
 for r in range(1,129):
  c=comb(2*r,r)
  constant=sum((-1)**j*comb(2*r,r+j) for j in range(r+1))
  derivative=sum(j*(-1)**(j-1)*comb(2*r,r+j) for j in range(1,r+1))
  need(2*constant==c and derivative==comb(2*r-2,r-1),'tail value/derivative')
  identity_cases+=1
 # All class members below2001, including both excluded and nonexcluded
 # subclasses; these are formula samples, not actual compiler histories.
 native=[]
 for r in range(1,2001,2):
  ds=digits(r)
  if ds[0] or 2 in ds:continue
  rec=classify(r);R=2*r+1;a27=native_direct(R,27);a81,terms=native_prime_power(R,4)
  need(a27==a81%27==rec['a_mod27'],'complete native ternary formula')
  rec.update(a_mod81=a81,streamed_binomial_coefficients=terms)
  native.append(rec)
 # Check complete orders in freely chosen arithmetic hosts only. These are
 # diagnostics for the general local implication, never claimed native H.
 hosts=[]
 for j in range(64):
  a=54*j+6;H=4*a+3;Delta=(a+1)*(a+3);O=order2(H);g=gcd(2*Delta,O)
  need(val(Delta,3)==2 and val(H,3)>=3 and val(g,3)==2,'exact local order component')
  mm=[]
  for d in (5,25,125):
   m=g//gcd(g,2*d);need(val(m,3)==2,'exact alias3 component');mm.append([d,m])
  for e in range(6):
   need(pow(2,2**e*(H-1),H)!=1 and pow(2,2**e*(H-3),H)!=1,'finite corroboration of all-e exclusion')
  hosts.append(dict(a=a,H=H,Delta=Delta,order=O,g=g,alias_moduli=mm))
 # Genuine half-binomial formula at parameters satisfying the known kernel
 # range and population prerequisites, but not an instantiated computation.
 R=511999;q=32;r=(R-1)//2;fixture=classify(r)
 need(R%4==3 and 3*q+1<=R<q**4 and R.bit_count()==3*5+2,'kernel numerical prerequisites')
 a81,terms=native_prime_power(R,4)
 need(a81%27==6 and fixture['excludes_both_tests'],'large formula exclusion')
 fixture.update(q=q,t=5,popcount_R=R.bit_count(),v2_a=R.bit_count()-2,a_mod81=a81,streamed_binomial_coefficients=terms,kernel_numeric_prerequisites=True,compiler_history=False,X_Y_H_materialized=False)
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,scope='Exact digit-class restriction on native half-binomial parameters; v3(m)=2 and all-e failure of both power tests on that class. No actual compiler-history occurrence, full zero, or language conclusion.',central_binomial_checks=central,tail_identity_cases=identity_cases,native_formula_samples=native,arithmetic_order_hosts=hosts,kernel_range_population_fixture=fixture,full_compiler_histories_materialized=0,new_complete_source_emitted=False,predecessor_code_executed=False)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True)
 group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 ns=ap.parse_args();out=verify(ns.root)
 if ns.expect:need(exact(out,loads(ns.expect.read_bytes())),'type-exact saved receipt')
 else:ns.output.write_text(json.dumps(out,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: exact native ternary class, v3(m)=2, both all-e power-test exclusions; history occurrence unresolved')
if __name__=='__main__':main()
