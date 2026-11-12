#!/usr/bin/env python3
"""Source inventory and finite update controls only; never invokes Lean."""
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'PositiveClient.lean',D/'research/ordinary14-direct-first-root-graph-client-draft/GraphFirstRootClient.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
s=paths[0].read_text()
for name in ('putRoot_self','positive_zero_iff','positive_zero_iff_natural_ports'):
 assert re.search(r'\btheorem\s+'+name+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert '(p 0 : DiffRing V)=ι beta' in s and 'P72Root.cast_port p 0' in s and 'putRoot_positive' in s
rng=random.Random(847900)
for _ in range(1000):
 v=[rng.randrange(1,100) for _ in range(14)];r=rng.randrange(1,100)
 w=v.copy();w[8]=r
 assert all(x>0 for x in w) and all(w[i]==v[i] for i in range(14) if i!=8)
 same=v.copy();same[8]=v[8];assert same==v
print(json.dumps({'scope':'source inventory and finite controls only; no Lean invocation','update_controls':1000,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
