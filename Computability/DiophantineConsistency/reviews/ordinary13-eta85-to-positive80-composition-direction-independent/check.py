from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
base=P('research/ordinary13-eta85-to-positive80-composition-draft')
files=[base/'Eta85ToPositive80.lean.src',base/'README.md',base/'check.py',base/'receipt.json',P('research/ordinary13-natural89-r-replacement-model-draft/Natural89MixedBridge.lean.src'),P('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),P('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src'),P('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src'),P('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),P('research/ordinary13-eta85-forced-map-composition-draft/Eta85ForcedMap.lean.src'),P('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),P('research/ordinary13-natural89-to-positive80-model-draft/PositiveUnit80Graph.lean.src'),P('research/ordinary13-natural89-direct-fy-model-draft/Natural89DirectFY.lean.src'),P('research/ordinary13-natural89-r-replacement-model-draft/Natural89RReplacement.lean.src')]
s=[p.read_text() for p in files]
def head(i,name):
 return re.sub(r'\s+',' ',s[i].split('theorem '+name,1)[1].split(':=',1)[0])
bridge80='PolynomialBridge (positiveShift (PositiveUnit80GraphDraft.literal (fun j => (ports K j:ℤ))))'
graphs=['JShifted89GraphDraft.literal','GammaShifted88GraphDraft.literal','WShifted87GraphDraft.literal','EtaShifted86GraphDraft.literal','EtaNaturalUnitGraphDraft.graph']
for i,name,src,dst in [(6,'bridge88',graphs[0],graphs[1]),(7,'bridge87',graphs[1],graphs[2]),(8,'parent86_bridge',graphs[2],graphs[3]),(9,'polynomialBridge',graphs[3],graphs[4])]:
 h=head(i,name); assert h.index(src)<h.index(' : ',h.index(src))<h.index(dst),(name,h)
for name in ('polynomialBridge85','native85'):
 h=head(0,name); assert h.count(bridge80)==1 and '(heta :' not in h and '(hrep :' not in h and graphs[4] in h
h=head(4,'bridge89');assert h.index(bridge80)<h.index(' : ',h.index(bridge80))<h.index(graphs[0])
h=head(4,'native85');assert 'EtaUnshift85TransportDraft.ForcedEta K' in h and bridge80 in h and graphs[4] in h
assert 'EtaUnshift85TransportDraft.ForcedEta K' in head(9,'forcedEta')
assert 'Natural89DirectFYDraft.directFY K' in s[4] and 'Natural89RReplacementDraft.rReplacement K' in s[4]
body=s[0].split('theorem polynomialBridge85',1)[1].split('/--',1)[0]
steps=['Natural89MixedBridgeDraft.bridge89 K h80','J88To89TransportDraft.bridge88 K h89','Gamma87To88TransportDraft.bridge87 K h88','W86To87TransportDraft.parent86_bridge K h87','Eta85ForcedMapDraft.polynomialBridge K h86']
assert [body.index(x) for x in steps]==sorted(body.index(x) for x in steps)
assert 'Natural89MixedBridgeDraft.native85 K (Eta85ForcedMapDraft.forcedEta K) h80' in s[0]
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'source_bridge_chain':'positiveShift80 -> 89 -> 88 -> 87 -> 86 -> 85','same_compact_tuple':True,'explicit_parent_bridge_count':1,'eta_forcing_and_replacement_are_unelaborated_dependencies':True,'lean_executed':False,'status':'Source signature audit only; imported providers, fixed endpoints, axiom reports and external ZFC/PDF binding remain open.'},sort_keys=True,indent=2))
