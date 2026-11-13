#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-ownzero-product-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'534957e6840dd56bd1f77e2149e7b38181a9d4529fd356a85bd821f99cc75188',A/'OwnZeroProduct74.lean':'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db',A/'check_source.py':'3f9589678186b092b58dcad1f95940708c81d3d6b7e5c40c47498489592a7669',A/'observation.json':'8865644a66ff831fc8143d1e037c2c4a25c679e0effe24c74173158ff7d1f714',D/'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean':'fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.lean':'5fbf0c5c27f5172dfda4b9684629a44378b22872a48a2a718f1542701e236d49',D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d',D/'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'}
tail=b'\nIndependent source review: [74 own-zero product](../../reviews/ordinary14-74-ownzero-product-independent/README.md).\n'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='3b5f608bf815cd48af9cda8040fbc989a7a31d9b18fce774a8151bc30fe8a4a5'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins[A/'README.md']
for p,h in pins.items():
 if p!=A/'README.md':assert sha(p)==h,(str(p),sha(p))
s=(A/'OwnZeroProduct74.lean').read_text();dep=(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.lean').read_text()
for t in ['pairEval (e*f) v=multiply (pairEval e v) (pairEval f v) := rfl','(hz : InternalZero (e-1) v) : Equivalent (pairEval e v) (natural (1:V))','product5 p q r s t=product5 p q r t s','rw [P74PositiveGuard.output_shape] at hz','rw [pairEval_mul,pairEval_mul,pairEval_mul,pairEval_mul] at h','rw [swap_last] at h','(product_of_zero p v hz) hmain haux hstrong']:
 assert t in s,t
for t in ['private theorem pairEval_mul','private theorem one_of_zero','theorem first_factor_units']:
 assert t in (dep+(D/'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean').read_text()),t
j=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_bytes());rows={z[0]:z[1:] for z in j['source']}
assert rows['P01']==['*','F0','F1'] and rows['P012']==['*','P01','Fa'] and rows['P0123']==['*','P012','Fs'] and rows['P01234']==['*','P0123','guard'] and rows['out']==['-','P01234',1]
def mul(p,q):return (p[0]*q[0]+p[1]*q[1],p[0]*q[1]+p[1]*q[0])
def prod(ps):
 x=ps[0]
 for p in ps[1:]:x=mul(x,p)
 return x
pairs=list(product(range(3),repeat=2)); count=0
for ps in product(pairs,repeat=5):
 assert prod(ps)==prod(ps[:3]+(ps[4],ps[3]));count+=1
for a,b in product(range(11),repeat=2):
 one=(1,0)
 subpair=(a+one[1],b+one[0])
 assert (subpair[0]==subpair[1])==(a==b+1)
first=(25,24);positive=0; negative_guard_cases=0
for q,r,s0,t in product(pairs,repeat=4):
 z=prod((first,q,r,s0,t))
 if z[0]==z[1]+1 and all(p[0]+1!=p[1] for p in (q,r,t)):
  assert all(p[0]==p[1]+1 for p in (first,q,r,s0,t));positive+=1
 if z[0]==z[1]+1 and s0[0]+1==s0[1]:negative_guard_cases+=1
assert positive>0 and negative_guard_cases>0
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(A/'observation.json').read_bytes() and not rr.stderr
print(json.dumps({'scope':'independent literal product, signed-pair algebra and finite controls; no Lean or graph-to-residue proof','pair_swap_cases':count,'sub_one_cases':121,'conditional_unit_positive_cases':positive,'guard_negative_before_other_exclusions':negative_guard_cases,'author_receipt_replayed':True,'reviewed_author_readme_sha256':pins[A/'README.md']},sort_keys=True,indent=2))
