#!/usr/bin/env python3
"""Produce a compact, unverified named DAG; never expand a power or sum."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parent.parent
PINNED = {
    D / 'research/nine-seed38-jones-named-formula-draft/FORMULA.md': '2ae78c33cf6f5f9a6096918aee8475c72adc205abbd6a954c69e7e06b457081c',
    D / 'research/nine-seed38-jones-named-formula-check/src/DiophantineConsistency/Norm38NamedFormula.lean': 'a5a8db6833252881c37016f3b28e006168db45a8119074b04572c8341d2593e6',
    D / 'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/SharingSeed38Syntax.lean': '9bde9c1eeaeda37dd59c097bcec2eb90df76ba07aa5a7e349ebe3eeae4b2e445',
}
for path, expected in PINNED.items():
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise RuntimeError(('source changed', str(path)))


def c(x): return ['const', x]
def v(x): return ['var', x]
def ref(x): return ['ref', x]
def fixed(x): return ['fixed', x]
def add(a, b): return ['add', a, b]
def sub(a, b): return ['sub', a, b]
def mul(a, b): return ['mul', a, b]
def pow_(a, n): return ['pow', a, n]
def nlit(x): return ['lit', x]
def npow(a, n): return ['pow', a, n]
def nref(x): return ['ref', x]
def nadd(a, b): return ['add', a, b]
def nsub(a, b): return ['sub', a, b]
def nmul(a, b): return ['mul', a, b]
def idx(x): return ['index', x]


nodes = []
def node(name, value):
    nodes.append({'name': name, 'expr': value})
    return ref(name)


L = npow(nlit(5), nlit(39))
b = node('b', add(add(fixed('y'), c(1)), v(0)))
B = node('B', pow_(b, nlit(5)))
q = node('q', pow_(B, L))
N = node('N', pow_(q, nlit(16)))
e = node('e', ['sum_star', 'k', mul(add(fixed('z'), ['pcoef', 'k']), pow_(B, nsub(L, ['expo', 'k'])))])
ell = node('ell', ['sum_range', 'r', nlit(38), pow_(B, npow(nlit(5), nadd(idx('r'), nlit(1))))])
lam = node('lambda', ['sum_range', 'r', nmul(nlit(4), L), pow_(B, idx('r'))])
g = node('g', add(v(1), c(1)))
theta = node('theta', sub(B, mul(c(2), fixed('z'))))
G = node('G', mul(mul(c(32), b), pow_(B, npow(nlit(5), nlit(38)))))
inner = add(add(mul(mul(c(2), sub(e, mul(fixed('z'), lam))), pow_(add(add(c(1), B), g), nlit(4))), mul(lam, B)), mul(mul(lam, B), pow_(q, nlit(4))))
left = mul(add(add(add(g, mul(e, pow_(q, nlit(3)))), mul(ell, pow_(q, nlit(5)))), mul(inner, pow_(q, nlit(7)))), sub(pow_(N, nlit(2)), N))
right = mul(add(add(add(sub(pow_(q, nlit(3)), mul(b, ell)), ell), mul(mul(theta, lam), pow_(q, nlit(3)))), mul(sub(B, c(2)), pow_(q, nlit(8)))), sub(pow_(N, nlit(2)), c(1)))
R = node('R', add(left, right))
h = node('h', add(v(2), c(1)))
s = node('s', add(v(3), c(1)))
w = node('w', add(v(4), c(1)))
phi = node('phi', v(5))
i = node('i', add(v(6), c(1)))
j = node('j', add(v(7), c(1)))
t = node('t', v(8))
U = node('U', mul(pow_(N, nlit(2)), w))
Y = node('Y', mul(pow_(N, nlit(2)), s))
M = node('M', mul(R, Y))
P0 = node('P', mul(mul(c(2), pow_(M, nlit(2))), U))
K = node('K', add(add(R, c(1)), mul(h, sub(P0, c(1)))))
A = node('A', mul(M, add(U, c(1))))
Bprime = node('Bprime', add(mul(c(2), R), c(1)))
W = node('W', mul(b, w))
C = node('C', add(add(Bprime, W), phi))
J = node('J', sub(mul(c(4), A), c(5)))
Q = node('Q', sub(mul(mul(c(3), W), C), mul(c(2), sub(pow_(W, nlit(2)), c(1)))))
D0 = node('D', add(mul(sub(pow_(A, nlit(2)), c(1)), pow_(C, nlit(2))), c(1)))
E = node('E', mul(mul(mul(i, J), D0), pow_(C, nlit(2))))
F = node('F', add(mul(sub(pow_(A, nlit(2)), c(1)), pow_(E, nlit(2))), c(1)))
Gp = node('Gprime', add(A, mul(F, sub(add(mul(C, D0), c(1)), A))))
H = node('H', add(Bprime, mul(j, C)))
I = node('I', add(mul(sub(pow_(Gp, nlit(2)), c(1)), pow_(H, nlit(2))), c(1)))
A0 = node('A0', add(mul(sub(pow_(P0, nlit(2)), c(1)), pow_(K, nlit(2))), c(1)))
A1 = node('A1', mul(mul(D0, F), I))
V0 = node('V0', add(pow_(A0, nlit(2)), c(2)))
V1 = node('V1', add(pow_(A1, nlit(2)), c(2)))
Bd = node('Bd', pow_(mul(J, F), nlit(2)))
Cd = node('Cd', pow_(add(mul(Q, F), mul(J, sub(H, C))), nlit(2)))
Dm = node('Dm', sub(sub(mul(pow_(K, nlit(2)), G), mul(mul(c(4), pow_(sub(C, mul(K, Y)), nlit(2))), G)), mul(mul(c(8), g), pow_(K, nlit(2)))))
Kc = node('Kc', mul(Bd, sub(mul(c(2), Dm), c(1))))
T = node('T', sub(add(mul(Bd, t), Cd), mul(Kc, add(Cd, mul(V0, V1)))))
node('output', sub(pow_(sub(add(pow_(T, nlit(2)), mul(pow_(Kc, nlit(2)), A0)), mul(mul(pow_(Kc, nlit(2)), pow_(V0, nlit(2))), A1)), nlit(2)), mul(mul(mul(c(4), pow_(T, nlit(2))), pow_(Kc, nlit(2))), A0)))

recipe = {
    'schema': 'named-ring-dag-with-finite-sum-macros-v1',
    'scope': 'unverified prototype; nine natural inputs; no claimed binary-operation count',
    'seed': 'SharingSeed38.seed CurrentWindowCarry2011.ports',
    'seed_type': 'Expr (Fin 39)',
    'coefficient_definitions': {'z': 'ExecutableJones.indexZ seed 0', 'y': 'ExecutableJones.indexY seed 0', 'pcoef': 'ExecutableJones.pCoefficient seed k', 'expo': 'ExecutableJones.codingExpo 38 4 k', 'star': 'ExecutableJones.codingStar 38 4'},
    'inputs': 9,
    'nodes': nodes,
    'output': 'output',
}
encoded = (json.dumps(recipe, sort_keys=True, indent=2) + '\n').encode()
path = P / 'recipe.json'
if sys.argv[1:] == ['--write']:
    with path.open('xb') as f: f.write(encoded)
elif sys.argv[1:] == ['--check']:
    if path.read_bytes() != encoded: raise RuntimeError('recipe differs')
    print(json.dumps({'status': 'PASS_SOURCE_PINNED_REGENERATION_ONLY', 'recipe_sha256': hashlib.sha256(encoded).hexdigest(), 'nodes': len(nodes), 'scope': 'No source-semantic binding, evaluation, binary-operation count or Lean theorem.'}, sort_keys=True))
else:
    raise SystemExit('expected --write or --check')
