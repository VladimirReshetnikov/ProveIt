#!/usr/bin/env python3
"""Fresh bounded exact algebra/finite-field evidence; no native tuple is run."""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'gamma83_native_next.md':'6cf4719fab43ad8873e372a5be0108192cc0a90cadccd84fe58d1e7a76cdaf74',
 'gamma83_next_arithmetic.md':'4298f6f64d4c9e1037901df3e0d50095ee126b9e31a82106db60643365d64f93',
 'complete83_gamma_native_finite_prime_avoidance.md':'93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96',
 'complete83_gamma_power_tests.md':'4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
}
def check(ok,why):
 if not ok:raise ValueError(why)
def sha(b):return hashlib.sha256(b).hexdigest()
def add(a,b):
 out=dict(a)
 for key,c in b.items():out[key]=out.get(key,0)+c
 return {key:c for key,c in out.items() if c}
def scale(a,c):return {key:v*c for key,v in a.items() if v*c}
def mul(a,b):
 out={}
 for ka,ca in a.items():
  for kb,cb in b.items():
   key=tuple(x+y for x,y in zip(ka,kb));out[key]=out.get(key,0)+ca*cb
 return {key:c for key,c in out.items() if c}
def main():
 deps=[]
 for name,digest in PINS.items():
  data=(ROOT/name).read_bytes();check(sha(data)==digest,'dependency '+name)
  deps.append({'path':name,'bytes':len(data),'sha256':digest,'executed_or_imported':False})
 one={(0,0):1};p={(1,0):1};k={(0,1):1}
 pminus=add(p,scale(one,-1));q=add(mul(k,pminus),one);u=mul(p,q)
 # Three formal Z[p,k] identities, proved and compared coefficientwise.
 identities=[
  ('u-1=(p-1)(kp+1)',add(u,scale(one,-1)),mul(pminus,add(mul(k,p),one))),
  ('u^2-p^2=(q-1)p^2(q+1)',add(mul(u,u),scale(mul(p,p),-1)),
   mul(mul(add(q,scale(one,-1)),mul(p,p)),add(q,one))),
 ]
 # Substitute k=2 independently into u, then check the discriminant square.
 u2={}
 for (a,b),c in u.items():u2[(a,0)]=u2.get((a,0),0)+c*(2**b)
 identities.append(('1+8u=(4p-1)^2 for k=2',add(one,scale(u2,8)),
                    mul(add(scale(p,4),scale(one,-1)),add(scale(p,4),scale(one,-1)))))
 for name,left,right in identities:check(left==right,name)
 order22=next(e for e in range(1,31) if pow(22,e,31)==1)
 check(order22==30,'native order30')
 field_rows=[];pair_residues=[]
 for f in range(1,31):
  roots=[x for x in range(1,31) if pow(x,f,31)==22]
  check(bool(roots)==(gcd(f,30)==1),'power-map image')
  if roots:
   check(len(roots)==1,'power root unique')
   value=roots[0]
   pvalues=[x for x in range(31) if x*(2*x-1)%31==value]
   square_roots=[x for x in range(31) if x*x%31==(1+8*value)%31]
   check(sorted((4*x-1)%31 for x in pvalues)==square_roots,'discriminant bijection')
   field_rows.append({'f_mod30':f,'u_mod31':value,'p_mod31':pvalues,
                      'discriminant_mod31':(1+8*value)%31})
  direct=[x for x in range(31) if pow(x*(2*x-1)%31,f,31)==22]
  check(direct==([] if not roots else pvalues),'direct930-case check')
  pair_residues.extend((f,x) for x in direct)
 allowed=sorted({f for f,p0 in pair_residues})
 check(allowed==[13,17,23,29],'allowed exponent residues')
 squares=sorted({x*x%31 for x in range(31)})
 check(22 not in squares,'excluded squarefree complement')
 record={'schema':'gamma83_composite_complement_certificate/v1',
         'helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,
         'polynomial_identities':[{'name':name,'coefficients':[[list(key),c] for key,c in sorted(left.items())]}
                                  for name,left,right in identities],
         'field31':{'order22':order22,'rows':field_rows,'allowed_exponent_residues':allowed,
                    'squares':squares,'direct_f_p_cases':930,'unit_power_cases':900,
                    'number_of_surviving_f_p_pairs':len(pair_residues)},
         'scope':{'evidence':'Exact polynomial identities and complete finite-field enumeration only.',
                  'native_formula_evaluated':False,'full83_zero_evaluated':False,
                  'compiler_or_predecessor_executed':False,'prime_complement_occurrence_proved':False,
                  'new_arithmetic_circuit_emitted':False,'repository_mutated':False}}
 parser=argparse.ArgumentParser();g=parser.add_mutually_exclusive_group(required=True)
 g.add_argument('--output');g.add_argument('--check');args=parser.parse_args()
 data=(json.dumps(record,indent=2,sort_keys=True)+'\n').encode()
 if args.output:
  with open(args.output,'xb') as f:f.write(data)
 else:check(Path(args.check).read_bytes()==data,'receipt mismatch')
 print(json.dumps({'status':'PASS','identities':len(identities),'field31':record['field31']},sort_keys=True))
if __name__=='__main__':main()
