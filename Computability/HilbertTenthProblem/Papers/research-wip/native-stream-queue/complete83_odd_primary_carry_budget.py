#!/usr/bin/env python3
"""Fresh carry/source congruence evidence. Predecessor bytes are inert only."""
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers')
NS=ROOT/'research-wip/native-stream-queue'
FILES=[NS/'complete83_shared_projection_scout.json',NS/'complete83_nondyadic_outer_family.md',NS/'complete83_odd_prime_boundary.md',NS/'complete75_half_binomial_compiler.md',ROOT/'1980/FIXED_RAW_UNIVERSAL_76_PROOF.md',ROOT/'1980/FIXED_RAW_UNIVERSAL_78_PROOF.md',ROOT/'verification/explore_fixed_raw_universal_76.py',ROOT/'verification/explore_fixed_raw_universal_78.py',NS/'complete75_half_binomial_compiler.py']

PINS={'FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', 'FIXED_RAW_UNIVERSAL_78_PROOF.md': 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'complete75_half_binomial_compiler.py': 'd6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2', 'complete83_nondyadic_outer_family.md': '42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23', 'complete83_odd_prime_boundary.md': '59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da', 'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c', 'explore_fixed_raw_universal_76.py': '011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0', 'explore_fixed_raw_universal_78.py': '10d5ed5809ccaf49b6006cf5758a40ed4f2bd05fed3f4747add3ea4c5d0b1639'}

def check(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def val(n,p):
 check(n!=0,'nonzero valuation argument');n=abs(n);v=0
 while n%p==0:n//=p;v+=1
 return v
def factval(n,p):
 out=0
 while n:n//=p;out+=n
 return out
def central(r,p):return factval(2*r,p)-2*factval(r,p)

def source_guards(raw):
 rows=json.loads(raw)['packet']['source'];by={r[0]:r for r in rows}
 expected=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],['qMF','*','q','MF'],['mask_factor','+','MC','qMF'],['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask']]
 for row in expected:check(by[row[0]]==row,'literal source '+row[0])
 check(len(rows)==83,'source rows')
 return {'source_rows':83,'literal_rows':len(expected),'rows':expected}

def formal_congruence():
 names=['A','m','z','K','MC','MF','c'];zero=(0,)*7
 def C(n):return {} if n==0 else {zero:n}
 def V(n):
  e=list(zero);e[names.index(n)]=1;return {tuple(e):1}
 def add(a,b,s=1):
  out=dict(a)
  for k,v in b.items():out[k]=out.get(k,0)+s*v
  return {k:v for k,v in out.items() if v}
 def mul(a,b):
  out={}
  for i,x in a.items():
   for j,y in b.items():
    k=tuple(a+b for a,b in zip(i,j));out[k]=out.get(k,0)+x*y
  return {k:v for k,v in out.items() if v}
 def scale(a,n):return {k:n*v for k,v in a.items() if n*v}
 A,m,z,K,MC,MF,c=[V(n) for n in names]
 output={}
 for eps in [-1,1]:
  T=add(mul(A,A),scale(A,eps));T2=mul(T,T);T3=mul(T2,T);T4=mul(T2,T2)
  F=mul(K,z)
  # H=16*m*(R+c), with the source constant +z retained.
  H=mul(m,T4)
  H=add(H,scale(mul(mul(m,F),T3),2),-1)
  H=add(H,scale(mul(add(MF,mul(m,add(z,C(1))),-1),T2),4))
  H=add(H,scale(mul(add(add(mul(m,F),MC),MF,-1),T),8))
  H=add(H,scale(add(add(mul(m,z),MC,-1),mul(m,c)),16))
  const=add(MC,mul(c,m),-1)
  bracket=add(add(MC,MF,-1),mul(K,const))
  P=add(scale(const,2),scale(mul(A,bracket),eps),-1)
  left=add(mul(add(C(2),scale(mul(A,K),eps),-1),H),scale(add(scale(mul(m,z),2),P,-1),16),-1)
  check(all(e[0]>=2 for e in left),'exact A-squared divisibility')
  quotient={tuple([e[0]-2]+list(e[1:])):v for e,v in left.items()}
  transcript=sorted((list(k),v) for k,v in quotient.items())
  output[str(eps)]={'integer_remainder_terms':len(quotient),'quotient_sha256':sha(json.dumps(transcript,separators=(',',':')).encode())}
 return {'variables':names,'identity':'16*(2-eps*A*K)*m*(R+c)-16*(2*m*z-P_eps,c(A)) is divisible by A^2 as an integer polynomial','cases':output}

def carry_checks():
 counts={'linear':0,'quadratic':0,'direct_factorial':0,'counterfamilies':0}
 trace=[]
 for p in [3,5,7,11,13]:
  for r in range(1,251):
   check(central(r,p)==val(math.comb(2*r,r),p),'small exact central binomial')
   counts['direct_factorial']+=1
  for b in range(1,6):
   for h in range(1,101):
    if h%p==0:continue
    r=p**b*h-1
    check(central(r,p)==b+central(h,p),'linear carry decomposition')
    counts['linear']+=1
    d=2*b+val(6,p);r=p**d*h-2
    check(central(r,p)==2*b+central(h,p),'quadratic carry decomposition')
    counts['quadratic']+=1
  for a in range(1,5):
   for L in range(1,7):
    h=p**L+1;r=p**a*h-1
    check(r%2==1 and val(r+1,p)==a and central(r,p)==a,'unbounded low-carry family')
    counts['counterfamilies']+=1;trace.append([p,a,L,r.bit_length(),central(r,p)])
 return {'counts':counts,'primes':[3,5,7,11,13], 'counterfamily_transcript_sha256':sha(json.dumps(trace,separators=(',',':')).encode()),'scope':'carry identities only; counterfamily is not a compiled source tuple'}

def obstruction_checks():
 records=[];d=25;B=1<<d;m=B-1
 for eps in [-1,1]:
  K=32*B+(32 if eps==-1 else 64)
  for n in [5,9]:
   A=(1<<(d*n))+1 if eps==-1 else (1<<(d*n+1))-1
   q=A*(A+eps)//2;J=(q-1)//m
   check(q==(B-1)*J+1,'family repunit')
   check(A>2*m*(3*K+8) and K+2>=4*m,'obstruction hypotheses')
   for MC in [2,B-2]:
    for MF in [B+3,2*B-5]:
     A0=q*q*(q*q-1)+(MC+q*MF)*J
     G=(1+q*K)*(q*q-1)
     check(math.gcd(G,A)==1,'affine coefficient unit')
     for c in [1,3]:
      z=((A0+c)*pow(G,-1,A*A))%(A*A)
      R=A0-G*z
      P=2*(MC-c*m)-eps*A*(MC-MF+K*(MC-c*m))
      check((R+c)%(A*A)==0 and (2*m*z-P)%(A*A)==0,'actual affine congruence')
      j=(2*m*z-P)//(A*A)
      check(P%2==1 and j%2==1 and j>=1,'odd multiplier')
      check(abs(P)<A*A//2+1,'P size')
      check(4*m*z>A*A and (K+2)*z>q,'raw slack violated')
      records.append({'eps':eps,'d':d,'n':n,'MC_dense':MC==B-2,'MF_high':MF==2*B-5,'c':c,'A_bits':A.bit_length(),'z_bits':z.bit_length(),'j':j,'congruence_root_sha256':sha(str(z).encode())})
 return {'cases':len(records),'records':records,'scope':'synthetic relaxed source numerals satisfying theorem scalar hypotheses; no actual compiled table or full positive zero'}

def result():
 deps={}
 for p in FILES:
  raw=p.read_bytes();check(sha(raw)==PINS[p.name],'dependency '+str(p))
  deps[str(p)]={'bytes':len(raw),'sha256':sha(raw)}
 return {'schema':'complete83-odd-primary-carry-budget-v1','helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,
         'source_guard':source_guards((NS/'complete83_shared_projection_scout.json').read_bytes()),
         'formal_congruence':formal_congruence(),'carry_checks':carry_checks(),'obstruction_checks':obstruction_checks(),
         'scope':{'predecessor_or_supplied_program_execution':False,'repository_mutation':False,'actual_compiler_outputs':0,'Pell_witnesses_materialized':0,'odd_primary_scale_success':False,'universal83_claim':False}}

def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');a=ap.parse_args()
 r=result()
 if a.output:
  with open(a.output,'x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 else:check(r==json.loads(Path(a.expect).read_text()),'receipt mismatch')
 print(json.dumps({'status':'PASS','carry_counts':r['carry_checks']['counts'],'source_congruence_cases':r['obstruction_checks']['cases']},sort_keys=True))
if __name__=='__main__':main()
