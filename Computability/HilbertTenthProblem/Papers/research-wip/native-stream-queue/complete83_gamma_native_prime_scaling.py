#!/usr/bin/env python3
"""Fresh exact checks for a native half-binomial prime-index scaling theorem."""
import argparse
import hashlib
import json
from math import comb, isqrt
from pathlib import Path

PINS={
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete83_gamma_power_tests.md':'4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b',
 'complete75_gamma87_compiler_order_filters.md':'43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
 '../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md':'44ed02164f61e410bb377b52aa292abf476e025eeea1052784f30d654a0522fa'}

def need(x,label):
 if not x:raise ValueError(label)
def sha(b):return hashlib.sha256(b).hexdigest()
def pairs(xs):
 out={}
 for k,v in xs:
  need(k not in out,'duplicate JSON key');out[k]=v
 return out
def loads(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def val(n,p):
 need(n>0,'positive valuation input');e=0
 while n%p==0:n//=p;e+=1
 return e
def signs(p):
 need(p>2 and prime(p),'odd prime')
 lam=-1 if p%4==3 else 1
 sig=-1 if p%8 in (3,5) else 1
 need(pow(p-1,(p-1)//2,p)==lam%p and pow(2,(p-1)//2,p)==sig%p,'quadratic characters')
 return lam,sig
def central(R):
 need(R>0 and R%2==1,'odd native index')
 return comb(R-1,(R-1)//2)
def direct(R,m):
 # Exact integer binomial coefficients, reduced only in the final modular sum.
 # R=1 uses the natural half-integral extension a_1=3/2 modulo odd m.
 need(R>0 and R%2==1 and m%2==1,'direct domain')
 r=(R-1)//2;x=pow(2,R,m);c=comb(2*r,r);xp=1;total=0
 for j in range(r+1):
  total=(total+c*xp)%m
  if j<r:c=c*(r-j)//(r+j+1)
  xp=xp*x%m
 return (x+1)*total*pow(2,-1,m)%m
def row_mod(R,p,k):
 # A second evaluator streams the entire Pascal row, with valuation and
 # unit maintained separately. It never constructs its huge coefficients.
 m=p**k;r=(R-1)//2;x=pow(2,R,m);xp=pow(x,-r,m)
 unit=1;e=0;tail=0
 for j in range(R):
  need(e>=0,'binomial valuation')
  coef=0 if e>=k else unit*p**e%m
  if j>=r:tail=(tail+coef*xp)%m
  if j<R-1:
   top=R-1-j;bottom=j+1
   while top%p==0:top//=p;e+=1
   while bottom%p==0:bottom//=p;e-=1
   unit=unit*(top%m)*pow(bottom%m,-1,m)%m
  xp=xp*x%m
 return (x+1)*tail*pow(2,-1,m)%m

def verify(root):
 raw={}
 for name,h in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==h,'pin '+name);raw[name]=b
 need(loads(raw['complete83_independent_gamma_scout.json'])['status']=='PASS','actual source receipt')
 records=[];zero_suffix=[];exceptional=0
 for p in (3,5,7,11,13,17,19,23,29,31):
  lam,sig=signs(p)
  for K in range(1,32,2):
   R=p*K;a=direct(R,p);ak=direct(K,p);c=central(R)%p;ck=central(K)%p;x=pow(2,K,p)
   need(c==lam*ck%p,'central index scaling')
   need((2*a-c)%p==sig*(2*ak-ck)%p,'diagonalized half-tail scaling')
   need(a==(sig*ak+(lam-sig)*ck*pow(2,-1,p))%p,'native parameter scaling')
   need(row_mod(R,p,1)==a,'independent whole-row evaluator')
   exception=x==p-1
   if exception:
    need(a==ak==0 and lam==sig,'X=-1 branch')
    exceptional+=1
   records.append(dict(p=p,K=K,a_pK=a,a_K=ak,C_pK=c,C_K=ck,lambda_sign=lam,sigma_sign=sig,X_minus_one=exception))
   zero_index=p*(K-1)+1
   az=direct(zero_index,p);cz=central(zero_index)%p
   need(az==ak and cz==ck,'zero last digit of R-1')
   zero_suffix.append(dict(p=p,K=K,R=zero_index,a_mod_p=az,C_mod_p=cz))
 repeated=[]
 for p in (3,5,7,11,13):
  lam,sig=signs(p)
  for K in (1,3,7,11):
   ak=direct(K,p);ck=central(K)%p
   for e in range(4):
    R=p**e*K;a=direct(R,p)
    expected=(sig**e*ak+(lam**e-sig**e)*ck*pow(2,-1,p))%p
    need(a==expected,'iterated p-power scaling')
    if e>=2:need(a==direct(R//(p*p),p),'square-factor removal')
    repeated.append(dict(p=p,K=K,e=e,a_mod_p=a))
 canonical=[]
 for e in (1,2,3):
  for f in (2,3):
   for z in (2,6):
    R=5**e*(1+5**f*z);a=row_mod(R,5,1)
    reduced=z+1;ar=direct(reduced,5);cr=central(reduced)%5
    want=ar if e%2==0 else (cr-ar)%5
    need(a==want and val(R,5)==e and R%4==3,'canonical congruence specialization')
    canonical.append(dict(e=e,Htime_exponent=f,z=z,R=R,reduced_index=reduced,a_mod5=a,
                          evidence='Congruence pattern only; not a supplied compiled history'))
 counterexamples=[]
 for R,wanted_a,wanted_v in ((395,274,2),(4575,372,3)):
  a=direct(R,625);independent=row_mod(R,5,4)
  need(a==independent==wanted_a,'two independent exact modulo625 tails')
  d=(a+1)*(a+3)%625;eR=val(R,5);eD=val(d,5)
  need(eD==wanted_v>eR and d!=0,'strict valuation counterexample')
  counterexamples.append(dict(R=R,K=R//5**eR,v5_R=eR,a_mod625=a,Delta_mod625=d,v5_Delta=eD,
                             full_compiler_history=False,full_kernel_tuple=False,a_materialized=False))
 # A large index is used only in the symbolic scaling formula: its residue
 # is proved by iteration, not independently checked by a huge tail sum.
 large=[];p=5;K=3;ak=direct(K,p);ck=central(K)%p
 for e in (1000,1001):
  R=5**e*K;a=(ak if e%2==0 else ck-ak)%5
  large.append(dict(p=p,K=K,e=e,R_bit_length=R.bit_length(),a_mod5=a,
                    Delta_mod5=(a+1)*(a+3)%5,H_mod5=(4*a+3)%5,
                    evidence='Exact symbolic consequence; huge tail not evaluated; no compiler history'))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,
             one_prime_checks=records,X_minus_one_checks=exceptional,zero_suffix_checks=zero_suffix,iterated_checks=repeated,canonical_congruence_examples=canonical,
             valuation_counterexamples=counterexamples,symbolic_large_indices=large,
             scope='Unrestricted exact half-binomial formula identities at odd indices, applicable conditionally to actual native histories. No history realization, whole-order bound, gamma83 language result, or new arithmetic circuit.',
             predecessor_code_executed=False,full_compiler_histories_materialized=0,new_complete_source_emitted=False)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 ns=ap.parse_args();out=verify(ns.root)
 if ns.expect:need(exact(out,loads(ns.expect.read_bytes())),'type-exact saved receipt')
 else:ns.output.write_text(json.dumps(out,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: native prime-index scaling, square-factor removal, and scoped valuation counterexamples')
if __name__=='__main__':main()
