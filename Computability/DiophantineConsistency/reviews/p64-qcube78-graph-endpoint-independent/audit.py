#!/usr/bin/env python3
"""Read-only graph, specialization and retained Lean receipt audit."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent.parent / 'research'
FILES = {
    'parent_graph': ('p64-qcube79-candidate/graph.json', 'd70bbed8b36895ffcf144f51bf78287e03fb2942d62c016ac9c845e691820b9b'),
    'graph': ('p64-qcube78-candidate/graph.json', '8037b90bdeb55c5fe91ab2db7e96b8c200f6c48c3ae6f0902e87435d1f1ba096'),
    'binding_source': ('fourteen-p64-qcube78-binding-draft/P64QCube78Binding.lean', '59d26b65d5ce2312746f3bf70bd43fddd89b3ebac8b170d7b62c83dcf6331255'),
    'binding_receipt': ('fourteen-p64-qcube78-binding-draft/lean-replay.json', '0b28a235fdfa00fdab699cd83f732a8ff1d63cdcec334066e05daf61f6f8e125'),
    'binding_log': ('fourteen-p64-qcube78-binding-draft/lean-replay.log', '07e57d13ef56820baf33559197a46512171acdce384d88a2fd4c6cd648d0f123'),
    'existence_source': ('fourteen-p64-qcube78-existence-draft/P64QCube78Existence.lean', 'a5e64c5dfeed7752d80546d6ff3b61cff314767d64682c173f935734e22b3af7'),
    'existence_receipt': ('fourteen-p64-qcube78-existence-draft/lean-replay.json', '21a13c2db0894d4768df4c224fd42d9c11510ac8cce99362e1337e57ed053d39'),
    'existence_log': ('fourteen-p64-qcube78-existence-draft/lean-replay.log', 'd3bd76eb4475485f3066e170775dd657b80f9b2426e0c91cec46f9d55d74f616'),
    'endpoint_source': ('p64-qcube78-ipra-draft/P64QCube78Endpoint.lean', 'f472f972edf2f8ec8d6e2cc343c36735475229ae22e7b0c37a34328022bd6a64'),
    'endpoint_receipt': ('p64-qcube78-ipra-draft/observations/attempt01/result.json', '4fb0b45ff8105aae88784f119aaee4966f5c8d67ca6e0e72e07da176ddb7fc27'),
    'endpoint_log': ('p64-qcube78-ipra-draft/observations/attempt01/compile.log', '41b797b72f5bd40ba6dbc96554ee6e88cf25cccf324aaeed25ab9f8376eaa720'),
}
sha = lambda b: hashlib.sha256(b).hexdigest()
data = {}
for key, (rel, digest) in FILES.items():
    data[key] = (RESEARCH / rel).read_bytes()
    if sha(data[key]) != digest:
        raise RuntimeError('hash mismatch: ' + key)
parent, graph = (json.loads(data[k]) for k in ('parent_graph', 'graph'))
old, new = parent['source'], graph['source']
assert len(old) == 79 and len(new) == 78
assert graph['witnesses'] == parent['witnesses'] and graph['fixed_numerals'] == parent['fixed_numerals'] and graph['output'] == parent['output']
assert [r for r in old if 'first_radicand' in r] == [
    ['first_radicand', '+', 'first_product', 1],
    ['A0', '-', 'first_unscaled_square', 'first_radicand']]
assert [r for r in new if r[0] == 'A0'] == [['A0', '-', 'first_unscaled_square', 'first_product']]
assert [r for r in old if r[0] == 'polynomial'] == [['polynomial', '-', 'sum3', 1]]
assert [r for r in new if r[0] == 'polynomial'] == [['polynomial', '-', 'sum3', 2]]
assert [r for r in old if r[0] not in ('first_radicand','A0','polynomial')] == [
    r for r in new if r[0] not in ('A0','polynomial')]
counts = dict(Counter(r[1] for r in new))
assert counts == {'*': 42, '+': 20, '-': 16}

# Full univariate polynomial evaluation over a finite field. It corroborates
# but does not prove the exact multivariate degree for the actual fixed ports.
prime = 1000003
def trim(a):
    while len(a)>1 and a[-1]%prime == 0: a.pop()
    return [x%prime for x in a]
def add(a,b,s):
    return trim([(a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%prime
    return trim(c)
v={n:[0,i+1] for i,n in enumerate(graph['witnesses'])}
v.update({n:[i+5] for i,n in enumerate(graph['fixed_numerals'])})
for n,op,l,r in new:
    a=v[l] if isinstance(l,str) else [l]; b=v[r] if isinstance(r,str) else [r]
    v[n]=add(a,b,1) if op=='+' else add(a,b,-1) if op=='-' else mul(a,b)
degree={n:len(v[n])-1 for n in ('A0','M','W','Na','Lt','polynomial')}
assert degree=={'A0':22,'M':34,'W':22,'Na':23,'Lt':2,'polynomial':68}
coef=lambda n:v[n][1] if n in graph['witnesses'] else v[n][0]
expected=(64*pow(coef('beta'),46,prime)*pow(coef('J'),46,prime)*pow(coef('w'),4,prime)*
          pow(coef('s'),14,prime)*pow(coef('eta')+coef('zeta'),2,prime)*pow(coef('gamma'),2,prime))%prime
assert expected==v['polynomial'][-1]==193218 and expected != 0

def axiom_log(namespace,names,axioms):
    return ''.join("'"+namespace+'.'+n+"' depends on axioms: ["+axioms+"]\n" for n in names).encode()
assert data['binding_log']==axiom_log('P64QCube78Binding',('first','main','strong','auxiliary','transport','output'),'propext')
assert data['existence_log']==axiom_log('P64QCube78Existence',('old_first_eq_zero','same_zero_iff','positive_zero_iff'),'propext, Classical.choice, Quot.sound')
assert data['endpoint_log']==axiom_log('P64QCube78Endpoint',('positiveBridge','native_equivalence','standard_equivalence','reference_equivalence'),'propext, Classical.choice, Quot.sound')
for part in ('binding','existence'):
    j=json.loads(data[part+'_receipt'])
    assert j['returncode']==0 and j['exact_expected_output'] and j['input_hashes']==j['after_hashes']
    assert j['log_sha256']==FILES[part+'_log'][1]
    for path,digest in j['input_hashes'].items(): assert sha(Path(path).read_bytes())==digest
    assert sha(Path(j['command'][-1]).read_bytes())==j['output_sha256']
ep=json.loads(data['endpoint_receipt'])
assert ep['exit']==0 and ep['log_sha256']==FILES['endpoint_log'][1]
for path,digest in ep['guards_before_after'].items(): assert sha(Path(path).read_bytes())==digest
assert sha(Path(ep['command'][-1]).read_bytes())==ep['object_sha256']
assert ep['guards_before_after']['/tmp/P64QCube78Existence.olean']==json.loads(data['existence_receipt'])['output_sha256']
print(json.dumps({'status':'PASS','input_hashes':{k:v[1] for k,v in FILES.items()},
                  'operation_counts':counts,'unchanged_parent_rows':76,'ray_prime':prime,
                  'ray_degrees':degree,'ray_output_leading_coefficient':expected,
                  'binding_exit':0,'existence_exit':0,'endpoint_exit':0,
                  'scope':'Structural output difference, one finite-field ray, retained binding/existence/endpoint receipts and current direct hashes; no new Lean, general degree, JSON binding, or full provider ancestry.'},indent=2,sort_keys=True))
