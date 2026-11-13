#!/usr/bin/env python3
"""Pin and compare proposed client sources; does not invoke Lean."""
from pathlib import Path
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
 raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
sources={
 'client81':(P/'Natural81RecipePorts.lean','4caa33b30a8534dbb7b00f59fa381251549102e5eef5ccc76e2a14a1a46937de'),
 'client82':(D/'research/ordinary14-natural82-recipe-port-bridge-draft/Natural82RecipePorts.lean','25e658a3e96d82b4c0d4591bf9ba160f120e7e12aa07db832c29064e86e5ffeb'),
 'endpoint81':(D/'research/ordinary14-natural-forcedj81-ipra-draft/Natural81Endpoint.lean','6b235dfcbc279f4d1110e323ead83aefa6c1f650ac6eaf1539a3cec65b8e79be'),
 'graph81':(D/'research/ordinary14-natural-forcedj81-lean-draft/P81NaturalForcedJ.lean','73fbd4a953a32c7c56a1e1b06f93c4da9aed950c8022f8988ac82c6c06353897'),
}
qualified={
 'AdaptiveEquationSyntax2011':'f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6',
 'HAExpressionAssembly':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e',
 'HAExpressionNoZeroEquiv':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
 'PRALanguage':'5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de',
 'IPRANativeTheory':'72702494753d27a888ed5b0a66c38f877cfaf836423374f3adc7f46a60c3d28b',
 'IPRAFoundationZFCMappedNegation':'9186acc49f486e0fbed0aa52ada450e253f028e64b18c5ee637e926edd4ad95c',
 'IPRAExpressionNative':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
 'IPRAStandardTheory':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
 'IPRAOrderErasure':'d14c6b50d1ee5c09bc6f3673d3bd9b3715ca2d9aba21c403a154fb6ff5da21d6',
 'IPRAReferenceInductionConversion':'e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9',
 'Compact44.CompactBytePortsModelIff':'6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d',
}
for name,h in qualified.items():sources['qualified:'+name]=(D/'Lean/DiophantineConsistency'/Path(*name.split('.')).with_suffix('.lean'),h)
s={}
for name,(path,want) in sources.items():
 data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==want,str(path);s[name]=data.decode()
expected=s['client82'].replace('Natural82','Natural81').replace('P82NaturalForced','P81NaturalForcedJ')
old='import Natural81Endpoint\nimport DiophantineConsistency.Compact44.CompactBytePortsModelIff\n'
new='import Natural81Endpoint\nimport P81NaturalForcedJ\n'+''.join('import DiophantineConsistency.'+n+'\n' for n in qualified)
assert old in expected and s['client81']==expected.replace(old,new,1)
assert 'namespace P81NaturalForcedJ' in s['graph81']
assert '(P81NaturalForcedJ.graph CompactSymbolicModelIff.p).output' in s['endpoint81']
assert 'theorem byteP_eq : byteP = p' in s['qualified:Compact44.CompactBytePortsModelIff']
assert 'open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv' in s['client81']
for n in ('polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert f'theorem {n}' in s['endpoint81'] and f'theorem {n}' in s['client81'] and f'exact Natural81EndpointDraft.{n}' in s['client81']
for n in ('expression_eq','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert f'#print axioms DiophantineConsistency.Natural81RecipePortsDraft.{n}' in s['client81']
print(json.dumps({'scope':'pinned source adaptation and selected declaration tokens only; no Lean, iPRA or file binding','pinned_sources':len(sources),'explicit_bare_imports':2,'explicit_qualified_imports':len(qualified),'axiom_commands_present_unexecuted':5,'output_graph':'P81NaturalForcedJ.graph byteP'},sort_keys=True,indent=2))
