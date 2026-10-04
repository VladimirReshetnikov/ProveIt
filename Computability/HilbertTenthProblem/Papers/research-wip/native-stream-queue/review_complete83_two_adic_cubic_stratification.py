#!/usr/bin/env python3
"""Independent finite checks; reads frozen notes/helpers only as inert bytes."""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path

WIP=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
AUTHOR=Path('/tmp/complete83_two_adic_cubic_stratification')
PINS={'.md':'ad55b60eaebf86eb7e82e1d600497f532d764680dc00c274a3c12607b2c7c9d9','.json':'5bb8a7c1ab2fb7c3cd5b6a30619ddefe49d69c5fa500125bd552fe787feaaf5b','.py':'35125c23453a82e16bd0b2818038be07040489567d67afdb4c9f2dcce546e115'}
DEPS={'complete83_even_radix_boundary.md':'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc','complete83_shared_projection_math.md':'1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c','complete83_dyadic_zero_offset_exclusion.md':'afa5bf412a150d61deb91e0c5b1eaa17f7f9423c254a93fd1d699221a285adc1'}

def ck(b,msg):
 if not b:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def val(n):
 ck(n>0,'positive valuation argument');z=0
 while n%2==0:n//=2;z+=1
 return z
def carries(a,b):
 carry=count=0
 while a or b or carry:
  s=(a&1)+(b&1)+carry
  carry=s>>1;count+=carry;a>>=1;b>>=1
 return count
def polynomial(coeff,z):
 acc=0
 for c in reversed(coeff):acc=acc*z+c
 return acc

def build():
 pins=[]
 for ext,expected in PINS.items():
  path=AUTHOR.with_suffix(ext);b=path.read_bytes();ck(sha(b)==expected,'author pin');pins.append({'path':str(path),'bytes':len(b),'sha256':expected})
 saved=json.loads(AUTHOR.with_suffix('.json').read_text())
 ck(saved['helper_sha256']==PINS['.py'] and saved['pins']==DEPS,'receipt source/dependency binding')
 for name,expected in DEPS.items():
  b=(WIP/name).read_bytes();ck(sha(b)==expected,'dependency pin');pins.append({'path':str(WIP/name),'bytes':len(b),'sha256':expected})
 counts=Counter();records=hashlib.sha256();roots=[]
 for r in range(3,768,2):
  cs=[comb(2*r,r+j) for j in range(4)]
  p=r.bit_count();k=val(r+1);ell=val(r+3);eta=val(r-1)
  actual_coeff=[val(c) for c in cs]
  carry_coeff=[carries(r-j,r+j) for j in range(4)]
  ck(actual_coeff==carry_coeff==[p,p-k,p+eta-k,p+eta-k-ell],'coefficient/carry valuations')
  counts['four_coefficient_rows']+=1
  for alpha in range(2,9):
   weights=[actual_coeff[j]+alpha*j for j in range(4)]
   tied=(k>=2 and alpha==k) or (k==1 and ell==3*alpha+1)
   normalized=None
   if tied:
    ck(min(weights)==p,'resonance minimum')
    normalized=[(c<<(alpha*j))//(1<<p) for j,c in enumerate(cs)]
    ck(all((cs[j]<<(alpha*j))==(1<<p)*normalized[j] for j in range(4)),'integral normalization')
    if k>=2:
     ck([val(c) for c in normalized]==[0,0,k+1,2*k],'linear normalized valuations')
    else:
     ck([val(c) for c in normalized]==[0,alpha-1,2*alpha+1,0],'cubic normalized valuations')
    residues=[]
    for precision in range(1,11):
     modulus=1<<precision
     found=[z for z in range(1,modulus,2) if polynomial(normalized,z)%modulus==0]
     ck(len(found)==1,'exhaustive unique odd residue')
     z=found[0]
     ck((normalized[1]+2*normalized[2]*z+3*normalized[3]*z*z)%2==1,'odd derivative')
     if residues:ck(z%(modulus//2)==residues[-1],'root compatibility')
     residues.append(z);counts['exhaustive_root_precisions']+=1
    roots.append({'r':r,'alpha':alpha,'kind':'linear' if k>=2 else 'cubic','roots_mod_2_to_2pow10':residues})
    counts['linear_resonances' if k>=2 else 'cubic_resonances']+=1
   else:
    ck(weights.count(min(weights))==1,'unique nonresonant minimum')
   for z in range(1,32,2):
    x=(1<<alpha)*z;value=polynomial(cs,x);observed=val(value)
    if not tied:
     claimed=p+min(0,alpha-k) if k>=2 else p+min(0,1-ell+3*alpha)
     ck(observed==min(weights)==claimed,'nonresonant exact formula')
    else:ck(value==(1<<p)*polynomial(normalized,z),'normalized whole identity')
    for t in range(2,alpha+1):
     threshold=3*t+1
     if not tied:criterion=min(weights)>=threshold
     elif p>=threshold:criterion=True
     else:criterion=polynomial(normalized,z)%(1<<(threshold-p))==0
     ck(criterion==(observed>=threshold),'complete local criterion')
     counts['threshold_comparisons']+=1
     if p<threshold and criterion:
      ck((k==alpha and k>=2) or (alpha==t and p==3*t and r==(1<<(3*t+1))-3),'low-central alternatives')
      counts['low_central_passes']+=1
    records.update(f'{r}:{alpha}:{z}:{observed}\n'.encode());counts['evaluated_positive_cubics']+=1
 # Independent full-polynomial vs cubic truncation for small even non-dyadic radices.
 trunc=[]
 for q in (12,20,24,28,36,40,44,48):
  t=val(q);ck(t>=2,'scale test input')
  for r in range(3,26,2):
   full=[comb(2*r,r+j) for j in range(r+1)]
   for w in (1,2,3,5):
    x=q*w;modulus=2*q**3
    a=polynomial(full,x)%modulus;b=polynomial(full[:4],x)%modulus
    ck(a==b,'full integer scale truncation')
    trunc.append([q,r,w,a]);counts['full_vs_cubic_congruences']+=1
 # Author's nine saved exceptional values are checked from exact coefficients.
 for row in saved['exceptional_family']:
  t=row['t'];r=(1<<(3*t+1))-3;z=row['odd_X_unit']
  ck(r==row['r'],'saved family r')
  v=val(polynomial([comb(2*r,r+j) for j in range(4)],(1<<t)*z))
  ck(v==row['cubic_v2'] and v>=3*t+1,'saved exception value')
  counts['author_exception_records']+=1
 # Large-index valuations only: no large binomial/Pell history is formed.
 symbolic=[]
 for t in range(2,65):
  r=(1<<(3*t+1))-3;p=r.bit_count();alpha=t
  weights=[carries(r-j,r+j)+alpha*j for j in range(4)]
  ck(p==3*t and weights[0]==weights[3]==p and weights[1]>p and weights[2]>p,'exceptional leading parity')
  symbolic.append({'t':t,'r_bits':r.bit_length(),'weighted_valuations':weights})
  for d in range(3*t+1,3*t+5):
   ck(2*r+1 < 3*(1<<d)+1,'sufficient compiler size exclusion')
   counts['compiler_size_inequalities']+=1
 return {'schema':'independent two-adic cubic stratification review v1','reviewer_sha256':sha(Path(__file__).read_bytes()),'frozen_inputs':pins,'status':'PASS','counts':dict(counts),'case_digest':records.hexdigest(),'exhaustive_residue_roots':roots,'truncation_digest':sha(json.dumps(trunc,separators=(',',':')).encode()),'exceptional_valuation_families':symbolic,'scope':{'human_read':'Full new author MD/PY/JSON; full even-radix boundary and dyadic-zero-offset notes; shared-projection proof authenticated and inherited, not recertified.','only_new_reviewer_executed':True,'native_masks_checked':False,'whole_source_zero_checked':False,'odd_prime_complete_criterion_claimed':False,'universal83_claimed':False,'new_circuit_or_paid_lift':False}}

def main():
 p=argparse.ArgumentParser();p.add_argument('--expect',type=Path);p.add_argument('--output',type=Path,default=Path('/tmp/review_complete83_two_adic_cubic_stratification.json'));a=p.parse_args()
 r=build();raw=(json.dumps(r,indent=2,sort_keys=True)+'\n').encode()
 if a.expect:ck(a.expect.read_bytes()==raw,'exact replay')
 else:a.output.write_bytes(raw)
 print(json.dumps({'status':'PASS','counts':r['counts'],'receipt_sha256':sha(raw)}))
if __name__=='__main__':main()
