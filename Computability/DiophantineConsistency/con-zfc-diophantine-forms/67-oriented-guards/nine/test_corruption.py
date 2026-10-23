#!/usr/bin/env python3
"""Focused negative controls: mutate in-memory circuits, never release files."""
import json
from check_nine import ROOT, require, evaluate, literal
p=1000003
body=json.loads((ROOT/'generated/split_108_order4_positive.json').read_text())
v={k:3 for k in body['variables']};ports={'beta':7,'K0':11,'MC':13,'MF':17}
want,_=literal(body,ports,v,p)
require(evaluate(body,ports,v,p)[0]==want,'positive control')
# Arithmetic-root tamper must change the evaluated polynomial.
bad=json.loads(json.dumps(body));root=bad['nodes'][bad['output']];root['kind']='add' if root['kind']=='sub' else 'sub'
require(evaluate(bad,ports,v,p)[0]!=want,'root operation corruption rejected')
# A different norm scale in metadata no longer matches the literal circuit.
bad=json.loads(json.dumps(body));bad['majorant_order']=3
require(literal(bad,ports,v,p)[0]!=want,'majorant order corruption rejected')
# Wrong threshold constant is not compatible with the fixed literal polynomial.
bad=json.loads(json.dumps(body));bad['threshold_scale_exponent']+=1
require(evaluate(bad,ports,v,p)[0]!=want,'threshold corruption rejected')
print('PASS: three independent in-memory corruption controls')
