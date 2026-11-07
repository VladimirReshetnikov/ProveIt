#!/usr/bin/env python3
"""Source-only coordinate/target inventory; does not parse or run Lean."""
import hashlib,json,re
from pathlib import Path
P=Path(__file__).resolve().parent;s=(P/'SharingSeed31BridgeDraft.lean').read_text()
def row(name):
 m=re.search(r'\bdef '+name+r'\b[^\n]*\n\s*!\[(.*?)\]',s,re.S);assert m;return [x.strip() for x in m.group(1).split(',')]
a,b=row('lift'),row('drop');assert a==[f'v {i}' for i in range(27)]+['(v 5 + 1) ^ 2']+[f'v {i}' for i in range(27,32)];assert b==[f'v {i}' for i in range(27)]+[f'v {i}' for i in range(28,33)]
for term in ['InternalZero (SharingSeed31Sextic.seed p) v','InternalZero (SharingSeed32Sextic.seed p) (lift v)','InternalZero (SharingSeed32Sextic.seed p) v','InternalZero (SharingSeed31Sextic.seed p) (drop v)']:assert term in s
assert 'theorem ' not in s and not re.search(r'\b(sorry|admit)\b',s)
out={'status':'pass','scope':'source text only; no Lean parsing, elaboration or proof','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'lift_entries':len(a),'drop_entries':len(b),'inserted_old_coordinate':27,'reconstructed_expression':a[27],'dropped_old_coordinate':27,'distinguished_coordinate_zero_preserved':True,'open_targets':['ForwardTarget','BackwardTarget']};(P/'bridge-result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,sort_keys=True))
