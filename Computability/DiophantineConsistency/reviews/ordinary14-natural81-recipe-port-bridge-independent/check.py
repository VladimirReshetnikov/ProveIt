#!/usr/bin/env python3
"""Independent direct-source/endpoint checks; no Lean invocation."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural81-recipe-port-bridge-draft/Natural81RecipePorts.lean':'4caa33b30a8534dbb7b00f59fa381251549102e5eef5ccc76e2a14a1a46937de',
'research/ordinary14-natural-forcedj81-ipra-draft/Natural81Endpoint.lean':'6b235dfcbc279f4d1110e323ead83aefa6c1f650ac6eaf1539a3cec65b8e79be',
'research/ordinary14-natural-forcedj81-lean-draft/P81NaturalForcedJ.lean':'73fbd4a953a32c7c56a1e1b06f93c4da9aed950c8022f8988ac82c6c06353897'}
q={'AdaptiveEquationSyntax2011':'f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6',
'HAExpressionAssembly':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e',
'HAExpressionNoZeroEquiv':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'PRALanguage':'5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de',
'IPRANativeTheory':'72702494753d27a888ed5b0a66c38f877cfaf836423374f3adc7f46a60c3d28b',
'IPRAFoundationZFCMappedNegation':'9186acc49f486e0fbed0aa52ada450e253f028e64b18c5ee637e926edd4ad95c',
'IPRAExpressionNative':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'IPRAStandardTheory':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
'IPRAOrderErasure':'d14c6b50d1ee5c09bc6f3673d3bd9b3715ca2d9aba21c403a154fb6ff5da21d6',
'IPRAReferenceInductionConversion':'e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9',
'Compact44.CompactBytePortsModelIff':'6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d'}
for module,digest in q.items():files['Lean/DiophantineConsistency/'+module.replace('.','/')+'.lean']=digest
s={}
for path,digest in files.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path
 s[path.rsplit('/',1)[-1]]=b.decode()
c=s['Natural81RecipePorts.lean'];e=s['Natural81Endpoint.lean'];g=s['P81NaturalForcedJ.lean'];b=s['CompactBytePortsModelIff.lean']
imports=re.findall(r'^import\s+(\S+)\s*$',c,re.M)
assert imports[:2]==['Natural81Endpoint','P81NaturalForcedJ']
assert len(imports)==13 and set(imports[2:])=={'DiophantineConsistency.'+n for n in q}
assert len(imports)==len(set(imports))
assert 'namespace P81NaturalForcedJ' in g and 'def graph (p : Fin 4 → ℤ) : Graph' in g
assert '(P81NaturalForcedJ.graph CompactBytePortsModelIff.byteP).output' in c
assert '(P81NaturalForcedJ.graph CompactSymbolicModelIff.p).output' in e
assert 'theorem byteP_eq : byteP = p' in b and 'congrFun decode_ports j' in b
assert 'open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv' in c
assert 'theorem expression_eq : expression = Natural81EndpointDraft.expression' in c
assert 'rw [CompactBytePortsModelIff.byteP_eq]' in c
names=('polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence')
def statement(src,name):
 m=re.search(r'\btheorem\s+'+name+r'\s*:\s*(.*?)\s*:=',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
for name in names:
 assert statement(c,name)==statement(e,name),name
 segment=c.split('theorem '+name,1)[1].split('\ntheorem ',1)[0].split('\nend ',1)[0]
 assert 'rw [expression_eq]' in segment and 'exact Natural81EndpointDraft.'+name in segment
names=('expression_eq',)+names
prints=re.findall(r'^#print axioms DiophantineConsistency\.Natural81RecipePortsDraft\.(\w+)$',c,re.M)
assert prints==list(names)
print(json.dumps({'scope':'bounded direct-source and endpoint-signature comparison; no Lean or file theorem',
 'bare_imports':2,'qualified_imports':len(q),'matching_endpoint_statements':4,
 'unexecuted_axiom_commands':len(prints),'byteP_to_symbolic_rewrite_inspected':True},sort_keys=True,indent=2))
