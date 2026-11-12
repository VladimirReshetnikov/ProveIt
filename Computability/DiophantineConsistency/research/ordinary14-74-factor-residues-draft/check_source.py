#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'FactorResidues74.lean').read_text()
for t in ('theorem main_shape','theorem aux_shape','theorem strong_shape','theorem restricted_residues','pairEval_residue','main_bad uv av cv dv','aux_bad av fv zv yv','strong_bad av fv iv'):
 assert t in s,t
cnt=0
for a,f,y,z in product(range(4),repeat=4):
 delta=(3+4*a+a*a)%4;Q=delta*(f*f-1)%4
 assert (y*y-Q*(y*y-z*z))%4 != 3
 assert (y*y-Q*(y*y-z*z))%4 == (Q*z*z+(1-Q)*y*y)%4
 cnt+=1
paths=[P/'FactorResidues74.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean']
print(json.dumps({'scope':'finite pattern and source controls; no Lean or graph theorem','aux_residue_cases':cnt,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
