#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Positive75To74.lean').read_text()
for t in ('theorem forward_map','theorem reverse_map','(hstrict : 1<v 13)','P72Root.ι_tsub','Ring75To74Draft.output_eval'):
 assert t in s,t
rng=random.Random(7475)
for _ in range(500):
 v=[rng.randrange(1,100) for _ in range(14)];w=v.copy();w[13]+=1;assert all(x>0 for x in w) and w[13]-1==v[13]
paths=[P/'Positive75To74.lean',D/'research/ordinary14-75-74-ring-client-draft/Ring75To74.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source-signature and coordinate controls only; no Lean or unconditional reverse','coordinate_controls':500,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
