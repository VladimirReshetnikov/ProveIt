#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'ModelEquivalence75To74.lean').read_text()
for t in ('(hd : Discrete (DiffRing V))','(hb : 0<beta)','Positive75To74Draft.forward_map p v hv hz','OwnZeroGuardStrict74Draft.strict_of_zero p beta K v hd hbeta hK hb hv hz','Positive75To74Draft.reverse_map p v hv hstrict hz','P72Root.cast_port p 0','P72Root.cast_port p 1'):
 assert t in s,t
paths=[P/'ModelEquivalence75To74.lean',D/'research/ordinary14-75-74-positive-map-draft/Positive75To74.lean',D/'research/ordinary14-74-ownzero-guard-strict-draft/OwnZeroGuardStrict74.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source-interface and hash checks only; no Lean or provider proof','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
