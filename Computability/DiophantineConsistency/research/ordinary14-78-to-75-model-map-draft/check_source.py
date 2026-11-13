#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Model78To75.lean').read_text()
for t in ('(hz : InternalZero (P78AuxRoot.graph p).output v)','InternalZero (P75NegativePell.graph p).output v','fiveSquares_eq_zero_iff','Ring78To75Draft.factor_evals p w','sub_eq_zero.mp ha','P75NegativePell.output_shape'):
 assert t in s,t
hits=0
for a,b,c,d,e in product(range(-2,3),repeat=5):
 squares=a*a+b*b+(c-1)*(c-1)+d*d+e*e
 if squares==0:
  assert (1+a)*(1+b)*c*(1+d)*(1+e)-1==0
  hits+=1
assert hits==1
r=D/'research/ordinary14-78-75-ring-client-draft';rr=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(r/'observation.json').read_bytes() and not rr.stderr
paths=[P/'Model78To75.lean',r/'Ring78To75.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean',D/'research/ordinary14-aux-root78-lean-draft/P78AuxRoot.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P75NegativePell.lean']
print(json.dumps({'scope':'source-interface and finite residual controls; no Lean or arbitrary-model proof','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'residual_zero_cases':hits,'residual_cases':5**5,'ring_receipt_replayed':True},sort_keys=True,indent=2))
