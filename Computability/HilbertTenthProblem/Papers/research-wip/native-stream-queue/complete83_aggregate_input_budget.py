#!/usr/bin/env python3
"""Fresh finite budget/carry checks. Frozen programs are never run or imported."""
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'complete83_source_coupled_input_lifting.md':'822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f',
 'complete83_source_coupled_input_lifting.py':'2d95450b60f1c480a5f9145b20e167567bc18ea984778d5c334b8c082043f2cd',
 'complete83_source_coupled_input_lifting.json':'cca7826dcc53c508cf16ecf8e5d3ddec006fbb707ee6dba23fcd19c083d0d93b',
 'complete83_odd_primary_carry_budget.md':'4b884c4d9cc6fd7100c67b98caee4ec9f968653e7a03c3d41558dc0d5cbc5f95',
 'complete83_odd_primary_carry_budget.py':'3b2bc4461caa6f438c3fd6d5cdf0f11d457953555b451e852ba76268c58845e3',
 'complete83_odd_primary_carry_budget.json':'f7933d99ee19edc51031392c8596e76df7f5d494a6d2e4de35223a4cd056b0de',
 'complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 'complete83_odd_prime_boundary.md':'59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da',
}

def check(truth,message):
 if not truth:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def valuation(value,p):
 check(value>0,'positive valuation');v=0
 while value%p==0:value//=p;v+=1
 return v

def authenticate():
 records=[]
 for name,pin in PINS.items():
  path=ROOT/name
  if not path.exists():path=Path('/tmp')/name
  raw=path.read_bytes();check(digest(raw)==pin,'dependency '+name)
  records.append({'name':name,'bytes':len(raw),'sha256':pin})
 return records

def source_guard():
 source=json.loads((ROOT/'complete83_shared_projection_scout.json').read_text())['packet']['source'];lookup={r[0]:r for r in source}
 rows=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],
 ['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],['C_after_alpha','-','q_minus_FZ','alpha'],
 ['scaled_t','*','twice_cell_bits','x'],['marked_rhs','-','C_after_alpha','scaled_t'],['W','-','marked_rhs','Z'],
 ['odd_index','+','scaled_t','inner_bits'],['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],
 ['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],['qMF','*','q','MF'],['mask_factor','+','MC','qMF'],
 ['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask'],['kinner','+','Kconstant','w'],
 ['innerC','*','kinner','marked_rhs'],['transport_partial','+','innerC','q_minus_F'],
 ['local_rhs','*','transport_quotient','repunit'],['norm_transport','-','transport_partial','local_rhs']]
 check(len(source)==83 and all(lookup[r[0]]==r for r in rows),'literal23row interface')
 return {'literal_rows':rows,'complete_source_rows':83,'array_evaluated':False}

def interval_checks():
 count=0;particular_only=0
 for S in range(1,97):
  for ell in range(1,25):
   positive=[k for k in range(S+1) if S-ell*k>0]
   N=len(positive);Kmax=(S-1)//ell
   check(N==(S+ell-1)//ell==Kmax+1,'exact interval cardinality')
   for H in range(1,49):
    actual={k%H for k in positive}
    expected=set(range(min(H,Kmax+1)))
    check(actual==expected,'particular CRT class criterion')
    check((len(actual)==H)==(H<=N)==(ell*(H-1)<S),'uniform criterion')
    particular_only+=int(H>N and 0 in actual)
    count+=1
 return {'S_interval':[1,96],'ell_interval':[1,24],'H_interval':[1,48],'cases':count,'particular_class_fits_but_uniform_fails':particular_only}

def capped_checks():
 count=0
 for a in range(1,9):
  for tau in range(0,3*a+2):
   for extra in range(0,4*a+2):
    g=min(tau,2*a);e=min(extra,max(2*a-tau,0));left=2*a-g-e;right=max(2*a-tau-extra,0)
    check(left==right,'capped exponent identity');count+=1
 return {'cases':count,'a_interval':[1,8],'includes_tau_exceeding_2a':True}

def factor(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p+=1
 if n>1:out[n]=out.get(n,0)+1
 return out

def binomial_checks():
 records=0;larger=0
 for r in range(3,1000,2):
  C=math.comb(2*r,r);primes={p:a for p,a in factor(r+1).items() if p%2}
  if not primes:continue
  odd=math.prod(p**a for p,a in primes.items());rad=math.prod(primes)
  choices={odd,rad}|{p for p in primes}
  for A in sorted(choices):
   H=G=E=1
   for p,a in factor(A).items():
    b=valuation(r+1,p);tau=b-a;unit=(r+1)//p**b
    c=valuation(C,p);extra=valuation(math.comb(2*unit,unit),p)
    check(c==a+tau+extra,'exact quotient carry decomposition')
    H*=p**max(3*a-c,0);G*=p**min(tau,2*a);E*=p**min(extra,max(2*a-tau,0))
   check(C%A==0 and H*G*E==A*A,'aggregate cap identity')
   check(G*E==math.gcd(A*A,C//A) and H==A**3//math.gcd(A**3,C),'two gcd forms')
   records+=1;larger+=int(H>A)
 return {'r_interval':[3,999],'cases':records,'cases_H_above_A':larger}

def source_coordinate_checks():
 cases=0
 for m in (15,31):
  for J in (101,251):
   q=m*J+1
   for K in (2,5):
    for z in (1,5):
     for d,T,x0 in ((2,3,10),(3,5,12)):
      F=K*z;S=q-(K+2)*z-2*d*x0;ell=2*d*T
      check(S>0,'synthetic base slack');limit=(S-1)//ell
      fixed_R=(q*q-z-q*F)*(q*q-1)+(2+q*(m+4))*J
      for k in (0,limit,limit+1):
       x=x0+k*T;alpha=S-ell*k;C=q-F-z-alpha-2*d*x
       w=(q-1)*(k+1);transport=1+z*(k+1)
       check(C==z and C-z==0,'unchanged C,W')
       observed_R=((q-1)*(q-F)+(q-F-z))*(q*q-1)+(2+q*(m+4))*J
       check(observed_R==fixed_R,'unchanged actual index formula')
       check((K+w)*C+q-F-transport*(q-1)==1,'literal transport unit')
       check((alpha>0)==(k<=limit),'source alpha interval')
       cases+=1
 return {'cases':cases,'scope':'fresh coordinate identities with relaxed scalar constants; w is a transport multiple, not an exponential'}

def local_example():
 r=503;R=1007;ell=6;A=21;u0=5;q=42;C=math.comb(2*r,r)
 c={p:valuation(C,p) for p in (3,7)};b={p:valuation(2**ell-1,p) for p in (3,7)}
 check(c=={3:4,7:1} and b=={3:2,7:1},'local valuations')
 H=math.prod(p**max(3-c[p],0) for p in c);check(H==49>A,'deeper local modulus')
 p=7;depth=b[p];precision=3-c[p];unit=(r+1)//p**depth;mod=p**precision
 F=lambda y:(unit*(r+2)+r*(r+2)*y+r*(r-1)*p**depth*y*y)%mod
 roots=[y for y in range(mod) if F(y)==0];check(len(roots)==1 and roots[0]%p,'simple unit root')
 image=[]
 for k in range(H):
  modulus=p**(depth+precision)
  X=(pow(2,R,modulus)-pow(2,u0+ell*k,modulus))%modulus
  check(X%p**depth==0,'normalized source map integrality');image.append((X//p**depth)%mod)
 check(len(set(image))==mod,'full deeper residue bijection')
 k0=image.index(roots[0]);check(k0==25,'local CRT representative')
 u=u0+ell*k0;modulus=2*q**3;X=(pow(2,R,modulus)-pow(2,u,modulus))%modulus
 total=0;power=1
 for j in range(r+1):total=(total+math.comb(2*r,r+j)*power)%modulus;power=power*X%modulus
 check(total==0 and ell*k0>q,'local full divisibility but source slack failure')
 return {'r':r,'R':R,'ell':ell,'A':A,'q':q,'u0':u0,'u':u,'central_valuations':c,'period_valuations':b,'Hreq':H,'k0':k0,'local_root':roots[0],'residue_images':image,'finite_sum_terms':r+1,'M_mod_2q3':total,'source_slack_at_q_impossible':True,'actual_compiler':False}

def build():
 deps=authenticate()
 return {'schema':'aggregate positive input budget v1','source_sha256':digest(Path(__file__).read_bytes()),'dependencies':deps,'source_guard':source_guard(),'interval_checks':interval_checks(),'capped_checks':capped_checks(),'binomial_checks':binomial_checks(),'source_coordinate_checks':source_coordinate_checks(),'local_example':local_example(),'status':'PASS','scope':{'predecessor_execution':False,'actual_compiler_outputs':0,'full_source_zeros':0,'automatic_carry_claim':False,'binary_condition_proved_for_enlarged_z':False,'uniform83_claim':False}}

def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
 result=build();raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if args.output:
  with args.output.open('xb') as f:f.write(raw)
 else:check(raw==args.expect.read_bytes(),'exact receipt replay')
 print(json.dumps({'status':'PASS','interval_cases':result['interval_checks']['cases'],'capped_cases':result['capped_checks']['cases'],'binomial_cases':result['binomial_checks']['cases'],'receipt_sha256':digest(raw)}))
if __name__=='__main__':main()
