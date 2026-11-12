#!/usr/bin/env python3
"""Source and finite arithmetic controls only; does not invoke Lean."""
from pathlib import Path
import hashlib, json, random
P = Path(__file__).resolve().parent
D = P.parents[1]
s = (P / 'Predecessors82.lean').read_bytes()
assert hashlib.sha256(s).hexdigest() == '9b17307ba0245cf02d3f944510daab2560f34b1ba31f2b93323c279bf12d0d3e'
t = s.decode()
for name in ('delta_gt_one', 'f_nonzero', 'y_nonzero', 'predecessors_of_factor_equations'):
    assert 'theorem ' + name in t
assert '(ha : 0 ≤ a) (hell : 0 ≤ ellPart)' in t
assert '(hfirst :' in t and '(hstrong :' in t and '(haux :' in t
assert 'ModelDifferenceRing.one_le_of_pos' in t and 'HasThreePredecessors w' in t
assert 'sorry' not in t and 'admit' not in t
partial = (P / 'PartialShift82To74.lean').read_bytes()
assert hashlib.sha256(partial).hexdigest() == '33b1d66bc3ab8010d83b91bff8604b015a3df000630a8d09fabbd77aa3e30a7e'
bound = (P / 'GraphPredecessors82.lean').read_bytes()
assert hashlib.sha256(bound).hexdigest() == '7972ddb132643d0fd46bfd66e200bdf80a48e5d0df1b75f719b9c4ef5db5de54'
partial, bound = partial.decode(), bound.decode()
assert 'theorem internalZero_iff_partial' in partial
for name in ('strong_cut', 'aux_cut', 'a_nonnegative', 'predecessors_of_zero'):
    assert 'theorem ' + name in bound
assert '(hbeta : (p 0 : DiffRing V) = ι beta) (hb : 0 < beta)' in bound
for name in ('restricted_residues', 'factor_units_of_zero', 'unit_iff_one',
             'predecessors_of_factor_equations'):
    assert name in bound
assert all(token not in partial + bound for token in ('sorry', 'admit'))
def load(path, digest):
    b = path.read_bytes()
    assert hashlib.sha256(b).hexdigest() == digest
    return json.loads(b)
g82 = load(D / 'research/ordinary14-root74-natural-forced82/candidate.json',
           '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a')
g74 = load(D / 'research/ordinary14-positive-guard74/candidate.json',
           'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093')
def calc(g, values, modulus):
    e = values.copy()
    for n, op, x, y in g['source']:
        x = x if type(x) is int else e[x]
        y = y if type(y) is int else e[y]
        e[n] = (x*y if op == '*' else x+y if op == '+' else x-y) % modulus
    return e
rng = random.Random(148274)
for modulus in (4, 17, 1009):
    for _ in range(100):
        values82 = {n: rng.randrange(-10, 11) for n in g82['witnesses'] + g82['fixed_numerals']}
        values74 = {n: values82['n_' + n] + (0 if i in (3, 8, 11) else 1)
                    for i, n in enumerate(g74['witnesses'])}
        values74.update({n: values82[n] for n in g74['fixed_numerals']})
        e82, e74 = calc(g82, values82, modulus), calc(g74, values74, modulus)
        assert e82['out'] == e74['out']
        a, i, f, y, v = (e74[x] for x in ('a', 'I', 'f2', 'y2', 'V'))
        delta = a*a + 4*a + 3
        assert e74['Fs'] == (1 + i*i - delta*(f-1)) % modulus
        assert e74['Fa'] == (y - delta*(f-1)*(y-v*v)) % modulus
        assert e74['F0'] == (e74['r']**2 - e74['ell']*(e74['ell']+e74['k'])) % modulus
checks = 0
for a in range(21):
    delta = a*a + 4*a + 3
    assert delta > 1
    for i in range(-20, 21):
        assert 1+i*i+delta != 1  # strong unit cannot hold at f=0
    for f in range(-10, 11):
        for v in range(-10, 11):
            assert delta*(f*f-1)*v*v != 1  # auxiliary unit cannot hold at y=0
            checks += 1
print(json.dumps({'scope': 'unelaborated source and finite controls only',
                  'factor_equations_and_nonnegativity_are_explicit_hypotheses': True,
                  'auxiliary_finite_controls': checks, 'delta_values': 21,
                  'partial_shift_and_factor_finite_controls': 300,
                  'own_zero_graph_linkage_is_source_proposal_only': True,
                  'no_lean_or_ipra_theorem': True}, sort_keys=True, indent=2))
