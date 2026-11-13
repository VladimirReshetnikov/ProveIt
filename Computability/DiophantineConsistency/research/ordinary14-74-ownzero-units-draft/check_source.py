#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'OwnZeroUnits74.lean').read_text()
for x in ('restricted_residues p v','factor_units_of_zero p beta v hbeta hb hJ hw hs hz hmain haux hstrong','exact h.2.2.2.1','theorem unit_iff_one','(unit_iff_one _ v).mp'):
 assert x in s,x
cnt=0
for a in range(16):
 for b in range(16):
  assert (a==b+1)==(a-b==1);cnt+=1
paths=[P/'OwnZeroUnits74.lean',D/'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean',D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean',D/'Lean/DiophantineConsistency/Compact44/FreeJ13.lean']
print(json.dumps({'scope':'source interfaces and finite signed-pair unit controls only; no Lean','unit_controls':cnt,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
