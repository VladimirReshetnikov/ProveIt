#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-78-to-75-model-map-draft'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'e38c55cdbd23f1142d974fa14781294812be65ab0a710d27f6f154d7e9c7f1ba',A/'Model78To75.lean':'9df593d1484be12f05e8cb4115ea5b8f0f233817b205a0bca39066014a3d60ec',A/'check_source.py':'dd08c34a78c9cd768a4b85fa58a65659d9f9b376a124f84e262c70093d4cf724',A/'observation.json':'1bd7d468c9779c5ab6059533a2dc014ac7df9cec5b17d3a4f9b91aafb901ea4a'}
tail=b"\nIndependent source review: [78 to 75 model map](../../reviews/ordinary14-78-to-75-model-map-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='98369a884f5976461c219b014983d4e6643c64293e29f41bc813cd0deff3a947'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
s=(A/'Model78To75.lean').read_text()
for t in ('(hz : InternalZero (P78AuxRoot.graph p).output v)','InternalZero (P75NegativePell.graph p).output v','fiveSquares_eq_zero_iff','⟨h0,h1,ha,hs,hg⟩','sub_eq_zero.mp ha','Ring78To75Draft.factor_evals p w','rw [hfactors.1,hfactors.2.1,hfactors.2.2.1,hfactors.2.2.2.1,hfactors.2.2.2.2]'):
 assert t in s,t
n=0;zeros=0
for A0,A1,aux,gap,guard in product(range(-2,3),repeat=5):
 square=A0*A0+A1*A1+(aux-1)**2+gap*gap+guard*guard
 out=(1+A0)*(1+A1)*aux*(1+gap)*(1+guard)-1
 if square==0:
  assert out==0 and (A0,A1,aux,gap,guard)==(0,0,1,0,0);zeros+=1
 n+=1
assert zeros==1
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interface and finite controls only; no Lean or reverse transfer','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'factor_controls':n,'square_zero_cases':zeros,'author_receipt_replayed':True},sort_keys=True,indent=2))
