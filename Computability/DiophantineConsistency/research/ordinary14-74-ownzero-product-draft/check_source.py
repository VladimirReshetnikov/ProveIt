#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'OwnZeroProduct74.lean').read_text()
for t in ('P74PositiveGuard.output_shape','theorem product_of_zero','theorem factor_units_of_zero','(hmain : pairResidue','(haux : pairResidue','(hstrong : pairResidue','rw [swap_last] at h'):
 assert t in s,t
cnt=0
for p,q,r,s0,t in product(range(-2,3),repeat=5):
 assert p*q*r*s0*t==p*q*r*t*s0
 cnt+=1
paths=[P/'OwnZeroProduct74.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean',D/'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.lean']
print(json.dumps({'scope':'finite factor order and source signature controls; no Lean or model graph proof','factor_order_controls':cnt,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
