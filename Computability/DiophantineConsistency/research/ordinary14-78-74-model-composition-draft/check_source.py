#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Model78To74.lean').read_text()
for t in ('ModelEquivalence7875Draft.zero_iff_natural_ports p v hb hv).mpr hz','ModelEquivalence7875Draft.zero_iff_natural_ports p v hb hv).mp hz','ModelDiscrete7574Draft.positive_zero_iff_natural_ports p hb','hfirst.trans'):
 assert t in s,t
paths=[P/'Model78To74.lean',D/'research/ordinary14-78-75-model-equivalence-draft/ModelEquivalence78To75.lean',D/'research/ordinary14-75-74-model-discrete-draft/ModelDiscrete75To74.lean']
print(json.dumps({'scope':'source-interface and hash controls only; no Lean or endpoint','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
