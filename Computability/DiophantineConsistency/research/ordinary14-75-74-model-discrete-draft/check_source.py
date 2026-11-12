#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'ModelDiscrete75To74.lean').read_text();base=(D/'Lean/DiophantineConsistency/ModelArithmetic.lean').read_text()
for t in ('theorem difference_ring_discrete : Discrete (DiffRing V)','one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hx','ModelEquivalence7574Draft.positive_zero_iff p beta K difference_ring_discrete hb hbeta hK','positive_zero_iff_natural_ports p difference_ring_discrete hb'):
 assert t in s,t
assert 'theorem model_discrete : Discrete (DiffRing V) := fun _ hx => one_le_of_pos model_one_le hx' in base
assert 'theorem model_one_le (a : V) (h : 0 < a) : 1 ≤ a := pos_iff_one_le.mp h' in base
paths=[P/'ModelDiscrete75To74.lean',D/'research/ordinary14-75-74-model-equivalence-draft/ModelEquivalence75To74.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean',D/'Lean/DiophantineConsistency/ModelArithmetic.lean']
print(json.dumps({'scope':'source signature, body correspondence and hash checks only; no Lean or provider proof','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
