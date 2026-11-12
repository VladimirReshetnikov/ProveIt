"""Boundary tests and finite proof-translation checks; no metatheorem claim."""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

import successor_eval as k
import zero_normal_control as old
import translate as t

ROOT = Path(__file__).resolve().parent
Z, V, ONE = t.Z, t.V, t.ONE
cases = []


def add(name, n, g, p, expected=None):
    a = k.infer(p, g, n)
    if expected is not None:
        assert a == expected, (name, a, expected)
    c = {'variables': n, 'context': g, 'goal': a, 'proof': p}
    k.check(c)
    back = t.translate_certificate(c, False)
    again = t.translate_certificate(back, True)
    assert again['goal'] == a
    cases.append((name, c))


# Canonical syntax, the only arithmetic primitive, and derived equality.
terms = [Z, ONE, ['s', ONE], ['i', ['v', 0], ONE, ['s', V]],
         ['i', ['v', 0], ['v', 1], ['i', V, ['v', 1], ['s', V]]]]
for i, a in enumerate(terms):
    add(f'refl_{i}', 2, [], t.ref(a), ['=', a, a])
for i, c in enumerate(terms):
    for j, h in enumerate([V, Z, ['s', V], ['i', V, ['v', 1], ['s', V]]]):
        a = ['v', 1]
        prev = a if c == Z else ['i', c, a, h]
        b = ['i', ['s', c], a, h]
        add(f'compute_{i}_{j}', 2, [], t.ev(t.ref(prev), t.ref(b)), ['=', b, k.sub(h, prev)])

s, u, r = ['v', 0], ['v', 1], ['v', 2]
g = [['=', s, u], ['=', s, r]]
add('derived_resolution', 3, g, t.resolve(['hyp', 0], ['hyp', 1], g, 3), ['=', r, u])
add('derived_symmetry', 3, g, t.symmetry(['hyp', 0], g, 3), ['=', u, s])
g2 = [['=', s, u], ['=', u, r]]
add('derived_transitivity', 3, g2, t.transitivity(['hyp', 0], ['hyp', 1], g2, 3), ['=', s, r])
for i, h in enumerate([V, Z, ['s', V], ['i', V, ['v', 1], ['i', ['v', 1], V, ['s', V]]]]):
    hs, hu = k.sub(h, s), k.sub(h, u)
    g = [['=', s, u], ['=', hs, r]]
    add(f'derived_congruence_{i}', 3, g, t.congruence(h, ['hyp', 0], ['hyp', 1], g, 3), ['=', r, hu])

# Both modes of DI, closure elimination, and an actually used induction hypothesis.
body = ['=', V, V]
for name, witness in [('progress_intro', Z), ('case_intro', ONE)]:
    add(name, 0, [], ['di', body, witness, t.ref(['s', V])], ['d', body])
compound = ['d', body]
add('compound_intro', 0, [], ['di', compound, Z, ['di', body, Z, t.ref(['s', V])]], ['d', compound])
a = ['i', ONE, Z, ['s', V]]
add('closure_elim', 0, [['q', body]], ['qe', a, ['hyp', 0], t.ref(Z)], ['=', a, a])
iterbody = ['=', ['i', V, Z, V], Z]
step = t.ev(['hyp', 0], t.ref(['i', ['s', V], Z, V]))
ind = ['di', iterbody, Z, step]
add('used_induction_hypothesis', 0, [], ind, ['d', iterbody])
goal = ['=', ['i', ONE, Z, V], Z]
add('existential_elim_used_closure', 0, [], ['de', goal, ind, ['qe', ONE, ['hyp', 0], t.ref(Z)]], goal)

# Hereditary substitution: a free counter becoming zero contracts beneath binders.
h = ['i', V, ['v', 1], ['s', V]]
assert k.sub(h, Z) == V
assert k.sub(['i', ONE, Z, ['i', ['v', 1], V, ['s', V]]], Z) == ['i', ONE, Z, V]

negative = []
base = cases[0][1]
for name, mutate in [
    ('bool_variables', lambda c: c.update(variables=True)),
    ('extra_field', lambda c: c.update(extra=0)),
    ('free_goal', lambda c: c.update(goal=['=', ['v', 2], ['v', 2]])),
    ('unknown_rule', lambda c: c.update(proof=['magic', Z])),
    ('boolean_variable', lambda c: c.update(proof=['refl', ['v', True]])),
    ('negative_variable', lambda c: c.update(proof=['refl', ['v', -1]])),
    ('noncanonical_zero_goal', lambda c: c.update(goal=['=', ['i', Z, Z, V], Z])),
    ('noncanonical_zero_proof', lambda c: c.update(proof=['refl', ['i', Z, Z, V]])),
    ('fake_step', lambda c: c.update(proof=['ev', t.ref(Z), t.ref(ONE)])),
    ('wrong_predecessor', lambda c: c.update(proof=['ev', t.ref(ONE), t.ref(['i', ONE, Z, V])])),
    ('negative_hyp', lambda c: c.update(proof=['hyp', -1])),
    ('boolean_hyp', lambda c: c.update(proof=['hyp', False])),
]:
    c = copy.deepcopy(base)
    mutate(c)
    try:
        k.check(c)
    except (ValueError, TypeError, IndexError, KeyError, RecursionError):
        negative.append((name, c))
    else:
        raise AssertionError(('negative accepted', name))

# Check the public acceptance contract in normal and optimized Python modes.
processes = 0
for flag in ([], ['-O']):
    for name, c in cases + negative:
        expected = name in {x[0] for x in cases}
        result = subprocess.run([sys.executable] + flag + [str(ROOT/'successor_eval.py')],
                                input=json.dumps(c), text=True, capture_output=True)
        assert (result.returncode == 0) == expected, (name, flag, result.stderr)
        assert not expected or result.stdout == 'ACCEPT\n'
        processes += 1

metrics = {}
for name in ['Research_computational_equality_code_checker.py', 'zero_normal_control.py', 'successor_eval.py']:
    source = (ROOT/name).read_text()
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + '\n'
    data = normalized.encode()
    excluded = {tokenize.ENDMARKER,tokenize.ENCODING,tokenize.NEWLINE,tokenize.NL,
                tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
    tokens = sum(x.type not in excluded for x in tokenize.generate_tokens(io.StringIO(normalized).readline))
    metrics[name] = {'bytes':len(data),'tokens':tokens,'ast_nodes':sum(1 for _ in ast.walk(tree)),
                     'gzip9':len(gzip.compress(data,compresslevel=9,mtime=0)),
                     'sha256':hashlib.sha256(data).hexdigest()}
report = {'python':sys.version,'positive_certificates':len(cases),
          'negative_certificates':len(negative),'command_line_checks':processes,
          'translation_roundtrips':len(cases),'metrics':metrics,
          'limitations':'Finite tests; universal equivalence is a written proof, not established by testing.'}
(ROOT/'test_results.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'certificates.json').write_text(json.dumps({'positive':dict(cases),'negative':dict(negative)},indent=2)+'\n')
print(json.dumps(report,indent=2))
