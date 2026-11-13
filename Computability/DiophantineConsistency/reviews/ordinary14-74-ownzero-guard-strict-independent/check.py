#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-ownzero-guard-strict-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'cda1db45b01d066a2b6bc4fde648739ce8a12f510e8a4a849cca0cecb24b6fcf',A/'OwnZeroGuardStrict74.lean':'d8d99e58177cdc6fde4fad5f79b577ce97023162656931691ce314141f98e1b8',A/'check_source.py':'60f377b743db7669d15c5caa6cd930d13d678871c3cbcd6ad2e4843c7d68fe0c',A/'observation.json':'789387e7e83f479cad0f6e3c045e77a8886db2a5321d77ebd3d117694431634a',D/'research/ordinary14-74-ownzero-units-draft/OwnZeroUnits74.lean':'668fb089dad1ced2867530cb7f95919eb584d49f4aa953903a7e2b6d526de43c',D/'research/ordinary14-positive-guard74-model-fact-draft/Guard74Strict.lean':'9eb4c453a74c0fb994c0dbbf0d3bd9d7bc7726e4a3a98d62941fafef04478565',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b',D/'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'}
tail=b'\nIndependent source review: [74 own-zero guard strictness](../../reviews/ordinary14-74-ownzero-guard-strict-independent/README.md).\n'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='c7cac670b02c61bd2e296082f655b1fc9038e6522189f1040eecffb511f58ab8'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins[A/'README.md']
for p,h in pins.items():
 if p!=A/'README.md':assert sha(p)==h,(str(p),sha(p))
s=(A/'OwnZeroGuardStrict74.lean').read_text();unit=(D/'research/ordinary14-74-ownzero-units-draft/OwnZeroUnits74.lean').read_text();fact=(D/'research/ordinary14-positive-guard74-model-fact-draft/Guard74Strict.lean').read_text()
for t in ['(hd : Discrete (DiffRing V))','(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)','(hz : InternalZero (P74PositiveGuard.graph p).output v)','guard_factor_one p beta v hbeta hb (hv 0) (hv 6) (hv 7) hz','rw [guard_eval p beta K v hbeta hK] at he','rw [hqcast] at he ⊢','linear_combination he','shifted_guard_gt_one hd','(ι (q beta v)) (ι (v 0*beta)) (ι (v 13)) hF ha hX (ι_nonneg K) hqX hh hbalance','apply ι_lt_ι.mp']:
 assert t in s,t
assert 'theorem guard_factor_one' in unit and 'theorem shifted_guard_gt_one' in fact
j=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_bytes());rows={z[0]:z[1:] for z in j['source']}
expected={'qm':['*','J','beta'],'q':['+',1,'qm'],'X':['*','q','w'],'qF':['-','q','F'],'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],'guard_base':['+','g27','qF'],'bt_quotient':['*','qm','h'],'guard':['-','guard_base','bt_quotient']}
for n,row in expected.items():assert rows[n]==row,(n,rows[n])
# Independently normalize the cut as a sparse polynomial over Z.
def add(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 out={}
 for x,xc in a.items():
  for y,yc in b.items():
   z=tuple(sorted(x+y));out[z]=out.get(z,0)+xc*yc
 return {k:v for k,v in out.items() if v}
one={():1};C,X,K,F,b,h=({(x,):1} for x in ('C','X','K','F','b','h'))
guard_minus_one=sub(sub(add(mul(C,add(X,K)),sub(add(one,b),F)),mul(b,h)),one)
balance=sub(sub(mul(C,add(X,K)),F),mul(b,sub(h,one)))
assert guard_minus_one==balance
n=0;zeroK=0
for J,beta,w,F,alpha in product(range(1,5),repeat=5):
 for K,h in product(range(3),range(1,5)):
  b=J*beta;q=1+b;X=q*w;C=q-F-alpha;guard=C*(X+K)+(q-F)-b*h
  if guard==1:
   assert q<=X and C*(X+K)-F==b*(h-1) and h>1
   n+=1;zeroK+= K==0
assert n>0 and zeroK>0
J,beta,w,F,alpha,K,h=1,2,1,1,1,-2,1
b=J*beta;q=1+b;X=q*w;C=q-F-alpha
assert C*(X+K)+(q-F)-b*h==1 and h==1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(A/'observation.json').read_bytes() and not rr.stderr
print(json.dumps({'scope':'independent source, guard-cut polynomial and finite scalar controls; no Lean or unconditional model result','guard_balance_polynomial_identity':True,'guard_one_cases':n,'guard_one_zero_K_cases':zeroK,'negative_K_partial_counterexample':[J,beta,w,F,alpha,K,h],'author_receipt_replayed':True,'reviewed_readme_sha256':pins[A/'README.md']},sort_keys=True,indent=2))
