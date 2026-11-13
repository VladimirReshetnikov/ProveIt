#!/usr/bin/env python3
"""Independent graph/source review and finite controls; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-direct-first-root-graph-client-draft'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

client = pinned(A / 'GraphFirstRootClient.lean', '864fb3935afd53711562656a3d5cbf7473d9182ded7face06b72416f6d72a78a').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-direct-first-root-graph-client-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == 'fec9a12aed8b3eb43007e81558d3851dd3c75c61f3ab70fb9a79d291f6d451a7'
paths = {
    'research/ordinary14-qcube84-lean-draft/P84QcubeGraph.lean': '552fa737fa0c36a58220053be90c4cdb35785d1fae53bc1c30bc15f8404104e9',
    'research/ordinary14-direct-pell79-lean-draft/P79DirectPell.lean': 'e5b138f7ea6b5782d66fde5016726e01c9045bf5ba13858dad1d923ca9622cdb',
    'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean': '92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f',
    'research/ordinary14-qcube84-probe/candidate.json': 'cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61',
    'research/ordinary14-direct-pell79/candidate.json': '5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507',
}
data = {name: pinned(D / name, value) for name, value in paths.items()}
old = json.loads(data['research/ordinary14-qcube84-probe/candidate.json'])
new = json.loads(data['research/ordinary14-direct-pell79/candidate.json'])
assert old['witnesses'] == new['witnesses']
assert old['witnesses'][8] == 'r' and old['fixed_numerals'] == new['fixed_numerals']

def structure(graph):
    tokens = {name: sha(('var:' + name).encode()) for name in graph['witnesses'] + graph['fixed_numerals']}
    dependencies = {name: {name} for name in tokens}
    def term(x): return ('int:' + str(x)) if isinstance(x, int) else tokens[x]
    for name, op, left, right in graph['source']:
        tokens[name] = sha(json.dumps([op, term(left), term(right)], separators=(',', ':')).encode())
        dependencies[name] = (dependencies[left] if isinstance(left, str) else set()) | (dependencies[right] if isinstance(right, str) else set())
    return tokens, dependencies

odag, odeps = structure(old)
ndag, ndeps = structure(new)
for field in ('A1', 'Fa', 'g72', 'guard'):
    assert odag[field] == ndag[field]
    assert 'r' not in odeps[field] and 'r' not in ndeps[field]
for statement in ('theorem common_fields', 'theorem scale_positive', 'theorem radicand_positive',
                  'theorem putRoot_positive', 'theorem old_first_eval', 'theorem direct_first_eval',
                  'theorem other_fields_ignore_root', 'theorem positive_first_coordinate_iff'):
    assert statement in client
assert '(hport : (p 0 : DiffRing V)=ι beta)' in client
assert '(hbeta : 0<beta) (hJ : 0<v 0)' in client
assert 'Function.update v 8 r' in client
assert 'positive_first_zero_iff' in client
assert 'theorem positive_first_zero_iff' in data['research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean'].decode()

# Exact first-residual scaling identity in Z[M,P,r,D].
def var(name): return {(name,): 1}
def add(a, b, sign=1):
    out = dict(a)
    for key, val in b.items(): out[key] = out.get(key, 0) + sign*val
    return {key: val for key, val in out.items() if val}
def mul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            out[key] = out.get(key, 0) + va*vb
    return {key: val for key, val in out.items() if val}
m, p, r, d = map(var, ('M', 'P', 'r', 'D'))
z = mul(m, add(p, r, -1))
lhs = add(mul(z, z), mul(mul(m, m), d), -1)
rhs = mul(mul(m, m), add(mul(add(p, r, -1), add(p, r, -1)), d, -1))
assert lhs == rhs

def replay(path, argv, receipt):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(path), *argv], cwd=D,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
    assert not run.stderr and run.stdout == receipt.read_bytes()

for dirname in ('ordinary14-qcube84-lean-draft', 'ordinary14-direct-pell79-lean-draft'):
    packet = D / 'research' / dirname
    replay(packet / 'make_graph.py', ['--check'], packet / 'observation.json')
replay(A / 'check_source.py', [], A / 'observation.json')
print(json.dumps({'scope': 'source and exact graph structure review only; no Lean invocation',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'graph_generators_replayed': 2,
                  'root_independent_identical_fields': ['A1', 'Fa', 'g72', 'guard'],
                  'exact_first_factorization': True,
                  'author_finite_controls_replayed': 100}, sort_keys=True, indent=2))
