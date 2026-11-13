#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Model75To78.lean').read_text()
for t in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hb : 0<beta)','(hv : ∀ j, 0<v j)','(hz : InternalZero (P75NegativePell.graph p).output v)','Positive75To74Draft.forward v','Positive75To74Draft.forward_positive v hv','Ring75To74Draft.output_eval p','restricted_residues p w','factor_units_of_zero p beta w hbeta hb','Ring75To74Draft.restricted_eval p','Ring75To74Draft.guard_eval p','Ring78To75Draft.factor_evals p z','fiveSquares_eq_zero_iff'):
 assert t in s,t
assert 'hK :' not in s and 'hstrict :' not in s
counts=0
for a,b,c,d,e in product(range(-2,3),repeat=5):
 # Four restricted factors exclude -1; the fifth guard is unrestricted.
 if a*b*c*d*e==1 and all(x!=-1 for x in (a,b,c,d)):
  assert (a,b,c,d,e)==(1,1,1,1,1)
  assert (a-1)**2+(b-1)**2+(c-1)**2+(d-1)**2+(e-1)**2==0
  counts+=1
assert counts==1
replayed=[]
for directory in ('ordinary14-75-74-positive-map-draft','ordinary14-74-ownzero-units-draft','ordinary14-78-75-ring-client-draft','ordinary14-direct-first-root-model-draft'):
 p=D/'research'/directory
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
 assert r.stdout==(p/'observation.json').read_bytes() and not r.stderr;replayed.append(directory)
paths=[P/'Model75To78.lean',D/'research/ordinary14-75-74-positive-map-draft/Positive75To74.lean',D/'research/ordinary14-74-ownzero-units-draft/OwnZeroUnits74.lean',D/'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean',D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean',D/'research/ordinary14-78-75-ring-client-draft/Ring78To75.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source-interface and finite factor controls; no Lean or model theorem','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'factor_assignments':5**5,'conditional_unit_cases':counts,'dependency_receipts_replayed':replayed},sort_keys=True,indent=2))
