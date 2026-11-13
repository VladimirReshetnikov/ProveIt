#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'Natural86Endpoint.lean').read_text()
for t in ('(P86NaturalCancel.graph CompactSymbolicModelIff.p).output','SameNoZero expression (positiveShift Root74PositiveBridgeDraft.expression)','exact he.mpr hz','exact he.mp hz','HAExpressionNoZeroEquiv.bridge expression (positiveShift Root74PositiveBridgeDraft.expression)','IPRAOrdinary12.bridge_of_positive _ Root74PositiveBridgeDraft.positiveBridge','IPRAExpressionNative.nativeNoZero expression','IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge','IPRAStandardTheory.provable_iff','IPRAReferenceInductionConversion.nativeToReference'):
 assert t in s,t
assert 'positiveShift expression' not in s
paths=[P/'Natural86Endpoint.lean',D/'research/ordinary14-natural-cancel86-ring-bridge-draft/Natural86Model.lean',D/'research/ordinary14-root74-positive-bridge-draft/Root74PositiveBridge.lean',D/'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean',D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean',D/'Lean/DiophantineConsistency/IPRAExpressionNative.lean']
print(json.dumps({'scope':'source-interface and hash controls only; no Lean, provider or proved endpoint','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
