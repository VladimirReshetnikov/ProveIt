#!/usr/bin/env python3
"""Compare two source-only clients and their pinned API declarations; no Lean."""
import hashlib, json
from pathlib import Path
D = Path(__file__).resolve().parents[2]
paths = {
 'natural82_client': ('research/ordinary14-natural82-recipe-port-bridge-draft/Natural82RecipePorts.lean', '25e658a3e96d82b4c0d4591bf9ba160f120e7e12aa07db832c29064e86e5ffeb'),
 'natural86_client': ('research/ordinary14-natural86-recipe-port-bridge-draft/Natural86RecipePorts.lean', '0f7011901bdbe9167e10370f3d16c844c5c123146952be5f6a8d385d9b0c4fec'),
 'natural82_endpoint': ('research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean', '2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b'),
 'byte_ports': ('Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean', '6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d'),
}
src = {}
for name,(path,digest) in paths.items():
    data=(D/path).read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest, path
    src[name]=data.decode()
names=('expression_eq','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence')
expected=src['natural86_client'].replace('Natural86','Natural82').replace('P86NaturalCancel','P82NaturalForced')
expected=expected.replace('open AdaptiveEquationSyntax2011 HAExpressionNoZeroEquiv', 'open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv')
expected+='\n'+''.join(f'#print axioms DiophantineConsistency.Natural82RecipePortsDraft.{n}\n' for n in names)
assert src['natural82_client']==expected
assert 'theorem byteP_eq' in src['byte_ports']
for n in names[1:]: assert f'theorem {n}' in src['natural82_endpoint']
print(json.dumps({'scope':'bounded source transcription/API token check; no Lean, iPRA or file binding','pinned_sources':len(paths),'proposed_declarations':list(names),'axiom_commands_unexecuted':len(names)},sort_keys=True,indent=2))
