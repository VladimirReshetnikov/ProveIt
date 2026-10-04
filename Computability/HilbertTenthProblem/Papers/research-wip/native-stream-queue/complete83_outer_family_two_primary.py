#!/usr/bin/env python3
"""New finite corroboration of a digit proof; never run/import predecessor programs."""
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
DEPS={
 str(ROOT/'complete83_shared_projection_scout.json'):'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 str(ROOT/'complete83_even_radix_boundary.md'):'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc',
 str(ROOT/'complete83_nondyadic_outer_family.md'):'42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23',
 str(ROOT/'complete83_odd_prime_boundary.md'):'59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da',
}
def require(ok,msg):
 if not ok: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def v2(n):
 require(n>0,'positive valuation input')
 return (n & -n).bit_length()-1

def source_guard(raw):
 rows=json.loads(raw)['packet']['source']; by={r[0]:r for r in rows}
 expected=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],
 ['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],
 ['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],
 ['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],['qMF','*','q','MF'],
 ['mask_factor','+','MC','qMF'],['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask']]
 require(len(rows)==83,'source row count')
 for row in expected:require(by[row[0]]==row,'literal row '+row[0])
 return {'source_rows':83,'literal_outer_rows':len(expected),'rows':expected,
         'scope':'literal interfaces only; no full-source/degree reconstruction'}

def expansions():
 # Coefficients in Q, low exponent first. Every variable has integer coefficients.
 # Sparse triples index exponents of Q,F,z; manipulate exact dictionaries.
 def add(a,b,sgn=1):
  out=dict(a)
  for k,v in b.items():out[k]=out.get(k,0)+sgn*v
  return {k:v for k,v in out.items() if v}
 def mul(a,b):
  out={}
  for i,x in a.items():
   for j,y in b.items():
    k=tuple(ii+jj for ii,jj in zip(i,j));out[k]=out.get(k,0)+x*y
  return {k:v for k,v in out.items() if v}
 def scale(a,s):return {k:s*v for k,v in a.items() if s*v}
 one={(0,0,0):1};Q={(1,0,0):1};F={(0,1,0):1};z={(0,0,1):1}
 Q2=mul(Q,Q)
 cases={}
 for shape in ['minus','plus']:
  q=add(scale(Q2,2),Q,-1) if shape=='minus' else add(Q2,Q)
  # In plus case q here is 2*q_actual; clear denominator16 term by term.
  q2=mul(q,q);q3=mul(q2,q);q4=mul(q2,q2)
  if shape=='minus':poly=add(add(add(add(q4,mul(F,q3),-1),mul(add(z,one),q2),-1),mul(F,q)),z)
  else:poly=add(add(add(add(q4,scale(mul(F,q3),2),-1),scale(mul(add(z,one),q2),4),-1),scale(mul(F,q),8)),scale(z,16))
  expected={}
  def put(e,c=0,f=0,zz=0):
   for ef,ez,v in [(0,0,c),(1,0,f),(0,1,zz)]:
    if v:expected[(e,ef,ez)]=v
  if shape=='minus':
   for args in [(8,16),(7,-32),(6,24,-8),(5,-8,12),(4,-3,-6,-4),(3,4,1,4),(2,-1,2,-1),(1,0,-1),(0,0,0,1)]:put(*args)
  else:
   for args in [(8,1),(7,4),(6,6,-2),(5,4,-6),(4,-3,-6,-4),(3,-8,-2,-8),(2,-4,8,-4),(1,0,8),(0,0,0,16)]:put(*args)
  require(poly==expected,'formal high polynomial '+shape)
  cases[shape]={'term_count':len(poly),'canonical_sha256':digest(json.dumps(sorted((list(k),v) for k,v in poly.items()),separators=(',',':')).encode())}
 return cases

def small_binomial_checks():
 count=0
 for r in range(3,1000,2):
  p=r.bit_count();k=v2(r+1);ell=v2(r+3);h=v2(r-1)
  observed=[v2(math.comb(2*r,r+j)) for j in range(4)]
  require(observed==[p,p-k,p+h-k,p+h-k-ell],'four coefficient valuations')
  count+=1
 return {'odd_r_interval':[3,999],'cases':count}

def digit_checks():
 records=[]; passing=0
 for d in [25]:
  B=1<<d;b=5
  for shape,K in [('plus',B+2),('minus',B+1)]:
   H=64*(4*d*K+4*d+1);width=H.bit_length();threshold=3*width+5
   nstar=threshold+(1-threshold)%4
   for n in [5,9,nstar,nstar+4]:
    D=d*n;Q=1<<D
    q=Q*(Q+1)//2 if shape=='plus' else Q*(2*Q-1)
    J=(q-1)//(B-1);t=v2(q)
    require((B-1)*J+1==q,'repunit')
    require(Q>H and Q>=32,'block size')
    for MC in [2,B-2]:
     for MF in [B,2*B-3]:
      for z in [1,4*d-3]:
       F=K*z
       S=(MC+q*MF)*J
       R=(q*q-z-q*F)*(q*q-1)+S
       require(0<R<q**4 and R%4==3,'source range/parity')
       require(0<S<2*q*q,'mask bound')
       r=(R-1)//2;p=r.bit_count();alpha=2*D+b
       modulus=B**(n-1)
       rep=(modulus-1)//(B-1)
       require(R%modulus==(z+MC*rep)%modulus,'whole low word')
       for j in range(2,n-1):require((R>>(d*j))&(B-1)==MC,'unmodified MC digit')
       require(v2(R+1)<2*d and v2(R+5)<2*d,'bounded denominator valuations')
       k=v2(r+1);el=v2(r+3);h=v2(r-1)
       weights=[p,p+alpha-k,p+2*alpha+h-k,p+3*alpha+h-k-el]
       require(min(weights)==p and weights.count(p)==1,'central unique minimum')
       require(p<=8*D+3<4*alpha,'higher terms strictly larger')
       if shape=='minus':
        V=R
        high=16*Q**4-32*Q**3+(24-8*F)*Q**2+(12*F-8)*Q-6*F-4*z-3
        eps=V//Q**4-high
        require(-1<=eps<=8,'minus lower carry')
        deficits={4:6*F+4*z+3-eps,6:8*F-24,7:33}
       else:
        V=16*R
        high=Q**4+4*Q**3+(6-2*F)*Q**2+(4-6*F)*Q-6*F-4*z-3
        eps=V//Q**4-high
        require(-1<=eps<=9,'plus lower carry')
        deficits={4:6*F+4*z+3-eps,5:6*F-3,6:2*F-5}
       for j,a in deficits.items():
        require(1<=a<H<Q,'deficit bound')
        require((V>>(D*j))&(Q-1)==Q-a,'actual complement digit')
        require((Q-a).bit_count()==D-(a-1).bit_count()>=D-width,'complement weight')
       lower=3*D-3*width+n-4
       require(p>=lower,'combined disjoint support bound')
       if n>=threshold:
        require(p>=3*D+1>=3*t+1,'eventual scale threshold')
        passing+=1
       records.append({'d':d,'shape':shape,'n':n,'MC_kind':'small' if MC==2 else 'dense',
                       'MF_kind':'low' if MF==B else 'high','z':z,'ell':width,
                       'threshold':threshold,'epsilon':eps,'central_population':p,
                       'population_lower_bound':lower,'t':t,'denominator_k':k,'denominator_ell':el,
                       'R_bits':R.bit_length()})
 return {'synthetic_relaxed_layouts':True,'actual_compiler_outputs':0,'Pell_witnesses':0,
         'cases':len(records),'above_uniform_threshold':passing,
         'max_R_bits':max(x['R_bits'] for x in records),'records':records,
         'scope':'fresh integer outer formulas under stated scalar bounds; actual z congruence and source zeros not constructed'}

def receipt():
 deps={}
 for name,pin in DEPS.items():
  raw=Path(name).read_bytes();require(digest(raw)==pin,'dependency '+name)
  deps[name]={'bytes':len(raw),'sha256':pin}
 return {'schema':'complete83-outer-family-two-primary-v1','helper_sha256':digest(Path(__file__).read_bytes()),
         'dependencies':deps,'source_guard':source_guard((ROOT/'complete83_shared_projection_scout.json').read_bytes()),
         'formal_expansions':expansions(),'coefficient_valuations':small_binomial_checks(),
         'digit_checks':digit_checks(),'scope':{'frozen_or_supplied_program_execution':False,
         'odd_primary_success_claim':False,'full_source_zero_claim':False,'universal83_claim':False}}

def main():
 ap=argparse.ArgumentParser();gp=ap.add_mutually_exclusive_group(required=True)
 gp.add_argument('--output');gp.add_argument('--expect');a=ap.parse_args()
 result=receipt()
 if a.output:
  with open(a.output,'x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 else:require(result==json.loads(Path(a.expect).read_text()),'receipt mismatch')
 print(json.dumps({'status':'PASS','digit_cases':result['digit_checks']['cases'],
                   'above_threshold':result['digit_checks']['above_uniform_threshold'],
                   'max_R_bits':result['digit_checks']['max_R_bits']},sort_keys=True))
if __name__=='__main__':main()
