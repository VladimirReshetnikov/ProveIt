#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Root74PositiveBridge.lean').read_text()
for t in ('(P74PositiveGuard.graph CompactSymbolicModelIff.p).output','ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat','CompactPortBoundsSlimDraft.port_bounds','Model78To74Draft.positive_zero_iff_natural_ports (V:=V) p hb.1','hpair.symm.trans (Root78PositiveBridgeDraft.positiveBridge V)'):
 assert t in s,t
paths=[P/'Root74PositiveBridge.lean',D/'research/ordinary14-78-74-model-composition-draft/Model78To74.lean',D/'research/ordinary14-root78-positive-bridge-draft/Root78PositiveBridge.lean',D/'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean',D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean']
print(json.dumps({'scope':'symbolic source interface and hash controls only; no Lean, physical bytes or endpoint','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
