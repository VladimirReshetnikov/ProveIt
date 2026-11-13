#!/usr/bin/env python3
"""Independent API/signature review for an unelaborated source client."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural82-recipe-port-bridge-draft/Natural82RecipePorts.lean':'25e658a3e96d82b4c0d4591bf9ba160f120e7e12aa07db832c29064e86e5ffeb',
'research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean':'2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b',
'Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean':'6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d',
'Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean':'3f863dde2c2c5bc3b5dd9789d2e2f5ae70c5856482979b577a4e405f6d7c019e',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
'Lean/DiophantineConsistency/HAExpressionAssembly.lean':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e'}
s={}
for path,digest in pins.items():
    data=(D/path).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,path
    s[path.rsplit('/',1)[-1]]=data.decode()
c=s['Natural82RecipePorts.lean'];e=s['Natural82Endpoint.lean'];b=s['CompactBytePortsModelIff.lean'];a=s['CompactFourPortByteAssembly2.lean'];p=s['CompactSymbolicModelIff.lean'];h=s['HAExpressionAssembly.lean']
assert re.search(r'^import Natural82Endpoint$',c,re.M)
assert re.search(r'^import DiophantineConsistency\.Compact44\.CompactBytePortsModelIff$',c,re.M)
assert 'open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv' in c
assert 'namespace DiophantineConsistency.HAExpressionAssembly' in h and 'def PolynomialBridge' in h
assert '(P82NaturalForced.graph CompactBytePortsModelIff.byteP).output' in c
assert '(P82NaturalForced.graph CompactSymbolicModelIff.p).output' in e
assert 'theorem byteP_eq : byteP = p' in b and 'congrFun decode_ports j' in b
assert 'Nat.ofDigits 256 (bytePorts j)' in a and 'theorem decode_ports :' in a
assert 'def p : Fin 4 → ℤ' in p
names=('expression_eq','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence')
for name in names:
    assert f'theorem {name}' in c
    assert f'#print axioms DiophantineConsistency.Natural82RecipePortsDraft.{name}' in c
assert 'theorem expression_eq : expression = Natural82EndpointDraft.expression' in c
assert 'rw [CompactBytePortsModelIff.byteP_eq]' in c
# Compare exact target statements after whitespace normalization, independently
# of a global textual substitution from the 86 client.
def statement(src,name):
    m=re.search(r'\btheorem\s+'+name+r'\s*:\s*(.*?)\s*:=',src,re.S);assert m,name
    return ' '.join(m.group(1).split())
for name in names[1:]:
    assert statement(c,name)==statement(e,name),name
    segment=c.split('theorem '+name,1)[1].split('\ntheorem ',1)[0].split('\nend ',1)[0]
    assert 'rw [expression_eq]' in segment and 'exact Natural82EndpointDraft.'+name in segment
print(json.dumps({'scope':'independent pinned source/signature checks, no Lean, axiom report, or external byte binding',
 'pinned_sources':len(pins),'matching_endpoint_statements':len(names)-1,'unexecuted_axiom_commands':len(names),
 'explicit_bridge_namespace_open':True,'byteP_to_symbolic_rewrite_inspected':True},sort_keys=True,indent=2))
