#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Root74Endpoint.lean').read_text();old=(D/'research/ordinary14-root78-ipra-endpoint-draft/Root78Endpoint.lean').read_text()
for t in ('native_of_positive _ Root74PositiveBridgeDraft.positiveBridge','standard_of_positive _ Root74PositiveBridgeDraft.positiveBridge','reference_of_positive _ Root74PositiveBridgeDraft.positiveBridge','positiveShift Root74PositiveBridgeDraft.expression','∼mappedNativeRefutation embedding'):
 assert t in s,t
for t in ('native_of_positive _ Root78PositiveBridgeDraft.positiveBridge','standard_of_positive _ Root78PositiveBridgeDraft.positiveBridge','reference_of_positive _ Root78PositiveBridgeDraft.positiveBridge'):
 assert t in old,t
paths=[P/'Root74Endpoint.lean',D/'research/ordinary14-root74-positive-bridge-draft/Root74PositiveBridge.lean',D/'research/ordinary14-root78-ipra-endpoint-draft/Root78Endpoint.lean',D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean']
print(json.dumps({'scope':'source-interface and hash controls only; no Lean or proved endpoint','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
