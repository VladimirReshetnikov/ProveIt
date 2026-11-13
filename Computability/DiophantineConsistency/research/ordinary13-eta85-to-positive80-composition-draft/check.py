from pathlib import Path
from hashlib import sha256
import json,re
p=Path('research/ordinary13-eta85-to-positive80-composition-draft')
fs=[p/'Eta85ToPositive80.lean.src',p/'README.md',
Path('research/ordinary13-natural89-r-replacement-model-draft/Natural89MixedBridge.lean.src'),
Path('research/ordinary13-natural89-r-replacement-model-draft/Natural89RReplacement.lean.src'),
Path('research/ordinary13-natural89-direct-fy-model-draft/Natural89DirectFY.lean.src'),
Path('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),
Path('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src'),
Path('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src'),
Path('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),
Path('research/ordinary13-eta85-forced-map-composition-draft/Eta85ForcedMap.lean.src'),
Path('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),
Path('research/ordinary13-natural89-to-positive80-model-draft/PositiveUnit80Graph.lean.src')]
s=[f.read_text() for f in fs]
for x in ['theorem polynomialBridge85','Natural89MixedBridgeDraft.bridge89 K h80',
 'J88To89TransportDraft.bridge88 K h89','Gamma87To88TransportDraft.bridge87 K h88',
 'W86To87TransportDraft.parent86_bridge K h87','Eta85ForcedMapDraft.polynomialBridge K h86',
 'theorem native85','Eta85ForcedMapDraft.forcedEta K']:
 assert x in s[0],x
for name in ['polynomialBridge85','native85']:
 head=s[0].split('theorem '+name,1)[1].split(':=',1)[0]
 assert head.count('(h80 : PolynomialBridge')==1 and '(heta :' not in head and '(hrep :' not in head
 assert 'positiveShift (PositiveUnit80GraphDraft.literal' in head
for i,parts in [(2,['replacement_of_cuts','Natural89DirectFYDraft.directFY','Natural89RReplacementDraft.rReplacement']),
 (6,['theorem bridge88','JShifted89GraphDraft.literal','GammaShifted88GraphDraft.literal']),
 (7,['theorem bridge87','GammaShifted88GraphDraft.literal','WShifted87GraphDraft.literal']),
 (8,['theorem parent86_bridge','WShifted87GraphDraft.literal','EtaShifted86GraphDraft.literal']),
 (9,['theorem forcedEta','EtaUnshift85TransportDraft.ForcedEta K','theorem polynomialBridge'])]:
 for x in parts:assert x in s[i],(i,x)
assert not re.search(r'\b(?:sorry|admit|unsafe|axiom)\b',s[0].split('/-!')[1].split('-/')[1])
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'single_explicit_parent_bridge':True,'eta_and_replacement_supplied_by_unelaborated_drafts':True,
 'source_bridge_direction_checked':True,'lean_executed':False,
 'status':'conditional source only; all graph/model/provider obligations remain open'},sort_keys=True,indent=2))
