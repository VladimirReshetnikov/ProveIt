#!/usr/bin/env python3
"""Source-only coordinate and target inventory; does not parse or run Lean."""
import hashlib, json, re
from pathlib import Path
root = Path(__file__).resolve().parent
source = (root / 'SharingSeed32BridgeDraft.lean').read_text()
def body(name):
    m = re.search(r'\bdef ' + name + r'\b[^\n]*\n\s*!\[(.*?)\]', source, re.S)
    assert m, name
    return [x.strip() for x in m.group(1).split(',')]
lift = body('lift')
drop = body('drop')
assert lift == [f'v {i}' for i in range(15)] + ['(beta * (v 1 + 1) + 1) ^ 2'] + [f'v {i}' for i in range(15, 33)]
assert drop == [f'v {i}' for i in range(15)] + [f'v {i}' for i in range(16, 34)]
for term in ['((p 0 : ℤ) : DiffRing V) = ι beta →', 'InternalZero (SharingSeed32Sextic.seed p) v', 'InternalZero (SharingSeed33.seed p) (lift beta v)', 'InternalZero (SharingSeed33.seed p) v', 'InternalZero (SharingSeed32Sextic.seed p) (drop v)']:
    assert term in source, term
assert 'theorem ' not in source and not re.search(r'\b(sorry|admit)\b', source)
out = {'status':'pass', 'scope':'source text checks only; no Lean parsing, elaboration, or proof', 'source_sha256':hashlib.sha256(source.encode()).hexdigest(), 'lift_entries':len(lift), 'drop_entries':len(drop), 'inserted_full_coordinate':15, 'reconstructed_expression':lift[15], 'dropped_full_coordinate':15, 'distinguished_coordinate_zero_preserved':True, 'open_targets':['ForwardTarget','BackwardTarget']}
(root/'bridge-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,sort_keys=True))
