from pathlib import Path
from hashlib import sha256
import json
p=Path('research/ordinary13-eta86-parent-bridge-inventory')
fs=[p/'Eta86ConditionalBridge.lean.src',p/'README.md',
Path('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),
Path('research/ordinary13-residue90-compact-tuple-client-draft/Residue90CompactTuple.lean.src'),
Path('Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean'),
Path('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean'),
Path('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean'),
Path('Lean/DiophantineConsistency/IPRAExpressionNative.lean'),
Path('research/ordinary13-freej88-lean-draft/P88PairModel.lean'),
Path('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean')]
ns=['ordinary13-natural-forced-w86','ordinary13-natural-forced-gamma87',
'ordinary13-natural-unit-product88','ordinary13-natural-unit-product89',
'ordinary13-unit-product80','ordinary13-residue-first81','ordinary13-qcube-main83',
'ordinary13-qcube-unscale84','ordinary13-aux-root87-36']
fs += [Path('research')/n/'candidate.json' for n in ns]
s=[f.read_text() for f in fs]; source=s[0]
for x in ['theorem selected_ports','theorem parent_bridge','(h86 : SameNoZero',
 'positiveShift IPRAOrdinary13.expression','IPRAOrdinary12.bridge_of_positive',
 'IPRAOrdinary13.positiveBridge','theorem child_bridge','(heta : EtaUnshift85TransportDraft.ForcedEta K)',
 'EtaUnshift85TransportDraft.polynomialBridge','theorem child_native']:
 assert x in source,x
assert 'def expression : Expr (Fin 13) := (FreeJ13.graph CompactSymbolicModelIff.p).output' in s[4]
assert 'theorem positiveBridge' in s[4] and 'theorem bridge_of_positive' in s[5]
assert 'theorem bridge' in s[6] and 'theorem equivalence_of_bridge' in s[7]
a=[json.loads(x) for x in s[10:]]
assert [len(g['source']) for g in a]==[86,87,88,89,80,81,83,84,87]
for child,parent,name,var in [(a[0],a[1],'w','n_w'),(a[1],a[2],'gamma','n_gamma'),(a[2],a[3],'J','n_J')]:
 assert child['witnesses']==parent['witnesses'] and child['fixed_numerals']==parent['fixed_numerals']
 assert sum(r==[name,'+',var,1] for r in parent['source'])==1
 assert [[var if x==name else x for x in r] for r in parent['source'] if r!=[name,'+',var,1]]==child['source']
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'exact_initial_edits':['w','gamma','J'],'conditional_source_interfaces_checked':True,
 'unproved_all_model_edges':7,'lean_executed':False,
 'status':'source-only inventory; no 86 bridge, proof replay or file/PDF binding'},sort_keys=True,indent=2))
