#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-pair-eval-ring-bridge-draft'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'ab57ced456f21624f5d56554c8b6f1d9b32a2dcf168b5d3436a2f8b18dcb4757',A/'PairEvalRingBridge.lean':'0fdb641db2008362ae3ec363bea66f6b4a4b475c1de2d5d00b7c1e9a81adc510',A/'check_source.py':'9637f28d96ae557f940b4e94a534f220fb085243f99426a4335c4c9cbf22c5b0',A/'observation.json':'d9921b3938b67ad983cd8ed48367de1afa477a97556ec7b7d71c58d609570b7e'}
tail=b"\nIndependent source review: [pair evaluation ring bridge](../../reviews/ordinary14-pair-eval-ring-bridge-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='83d13d78118e05191e5b50b57bf9d57fc62fb60b4b3b687edbbf025031a00820'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
s=(A/'PairEvalRingBridge.lean').read_text()
for t in ('split_evalRing e (fun j => ι (v j))','←evalSemiring_map ι e.splitNatural.1 v','←evalSemiring_map ι e.splitNatural.2 v','apply ι_injective','linear_combination hs + h','equivalent_trans (equivalent_symm he) h','equivalent_trans he h','five_positive_of_direct_first'):
 assert t in s,t
pairs=list(product(range(4),repeat=2));n=0;nontrivial=0
for P0,P1 in product(pairs,repeat=2):
 if P0[0]-P0[1]!=P1[0]-P1[1]:continue
 for q in pairs:
  for u in pairs:
   mul=lambda x,y:(x[0]*y[0]+x[1]*y[1],x[0]*y[1]+x[1]*y[0])
   a=mul(P0,q);b=mul(P1,q)
   assert (a[0]+u[1]==a[1]+u[0])==(b[0]+u[1]==b[1]+u[0])
   n+=1;nontrivial+=a[0]+u[1]==a[1]+u[0]
assert nontrivial>0
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source signatures, independent finite signed-pair controls; no Lean, graph or endpoint','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'product_replacement_controls':n,'true_equivalences':nontrivial,'author_receipt_replayed':True},sort_keys=True,indent=2))
