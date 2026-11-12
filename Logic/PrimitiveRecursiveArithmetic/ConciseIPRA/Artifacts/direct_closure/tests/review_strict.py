"""Targeted independent scoping regressions for the strict checker audit.

The cases exercise retained hypotheses, nested iterator binders, a nested
DE branch, and nested progression. The trusted checker files are not edited.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT
sys.path.insert(0, str(PACKAGE / 'code'))
import strict_q as new
import strict_old as old
from translate import counts, translate

Z = ['z']
V = lambda n: ['v', n]
S = lambda t: ['s', t]
E = lambda s, t: ['e', s, t]
I = lambda n, a, h: ['i', n, a, h]
Q = lambda b: ['q', b]
D = lambda b: ['d', b]


def refl(term):
    equation = ['zero', term, Z]
    return ['tr', E(V(0), new.shift(term)), equation, equation]


def certificate(parameters, context, goal, proof):
    return dict(parameters=parameters, context=context, goal=goal, proof=proof)


# Both y and x occur. The equation's two nested iterator binders enclose
# parameters a,b; the witness itself is a parameterized iterator.
left = I(V(0), V(1), I(V(0), V(3), V(5)))
right = I(V(0), V(1), I(V(0), V(4), V(5)))
matrix = E(left, right)
witness = I(V(0), V(1), S(V(0)))
body = old.witness_instance(matrix, witness)
target = old.successor_instance(body)
# Replace only the right inner initializer by the transport hole. Under
# the outer iterator's update the fresh template hole has index one.
template = new.shift(target)
template[2][3][2] = V(1)
step = ['tr', template, ['hyp', 1], refl(target[1])]
context = [E(V(0), V(1))]
cases = [
    ('old_retained_nested_iterator', old, 'old-to-q',
     certificate(2, context, D(matrix), ['prog', matrix, witness, step])),
    ('q_retained_nested_iterator', new, 'q-to-old',
     certificate(2, context, Q(body), ['prog', body, step])),
]

# Progression uses a retained D hypothesis; its DE branch uses both the
# newly opened Q hypothesis (index 0) and the shifted induction hypothesis
# (index 1). This tests two independently scoped local assumptions.
matrix = E(V(2), V(2))
body = E(V(1), V(1))
context = [D(E(V(2), V(2)))]
step = ['de', body, ['hyp', 1], ['qe', Z, ['hyp', 0], ['hyp', 1]]]
cases += [
    ('old_retained_de_branch', old, 'old-to-q',
     certificate(1, context, D(matrix), ['prog', matrix, V(0), step])),
    ('q_retained_de_branch', new, 'q-to-old',
     certificate(1, context, Q(body), ['prog', body, step])),
]

# An outer D-progress proof contains a second D-progress proof inside a
# DE/transport premise. Both must be translated, while preserving the
# scope of the outer induction variable in the inner elimination target.
inner_matrix = E(V(0), V(0))
inner_progress = ['prog', inner_matrix, Z, refl(S(V(0)))]
inner_equality = ['de', E(V(0), V(0)), inner_progress,
                  ['qe', V(1), ['hyp', 0], refl(Z)]]
outer_step = ['tr', E(V(2), V(2)), inner_equality, ['hyp', 0]]
outer_matrix = E(V(2), V(2))
cases.append(('old_nested_progress', old, 'old-to-q',
              certificate(1, [], D(outer_matrix),
                          ['prog', outer_matrix, V(0), outer_step])))

receipts = []
cli_runs = 0
outdir = ROOT / 'tests/review_certificates'
outdir.mkdir(exist_ok=True)
for name, source, direction, original in cases:
    target = new if source is old else old
    inverse = 'q-to-old' if direction == 'old-to-q' else 'old-to-q'
    source.check(original)
    translated = translate(original, direction)
    target.check(translated)
    recovered = translate(translated, inverse)
    source.check(recovered)
    if original['goal'] != translated['goal'] or original['context'] != translated['context']:
        raise RuntimeError('translation changed the sequent')
    before, steps = counts(original['proof'])
    after, _ = counts(translated['proof'])
    expected = before + (3 if direction == 'old-to-q' else 2) * steps
    if after != expected:
        raise RuntimeError('translation node count failed')
    for suffix, module, item in [('source', source, original),
                                 ('translated', target, translated),
                                 ('roundtrip', source, recovered)]:
        filename = outdir / f'{name}_{suffix}.json'
        filename.write_text(json.dumps(item, indent=2) + '\n')
        script = PACKAGE / 'code' / ('strict_old.py' if module is old else 'strict_q.py')
        for optimize in (False, True):
            command = [sys.executable] + (['-O'] if optimize else []) + [str(script)]
            run = subprocess.run(command, input=json.dumps(item), text=True,
                                 capture_output=True, timeout=10)
            if run.returncode or run.stdout.strip() != 'ACCEPT':
                raise RuntimeError(f'{name}/{suffix}: {run.stderr}')
            cli_runs += 1
    receipts.append(dict(name=name, nodes=before, progress=steps,
                         translated_nodes=after, verified_roundtrip=True))

# A control addressing the concrete uncovered risk: changing the retained
# hypothesis reference to the induction hypothesis must invalidate the
# nested-iterator source proof. Those equations have different shapes.
corrupted = deepcopy(cases[0][3])
corrupted['proof'][-1][2] = ['hyp', 0]
try:
    old.check(corrupted)
except (ValueError, TypeError, IndexError, KeyError):
    pass
else:
    raise RuntimeError('retained-hypothesis corruption was accepted')

# A genuine eigenvariable-escape attack: the major proves existence of a
# witness x=0 (via a gated matrix). The DE branch proves that fresh x is
# zero. It must not certify that the unrelated retained parameter a is zero.
gated_matrix = E(I(V(0), Z, V(2)), Z)
major = ['case', gated_matrix, Z, ['succ', V(0), Z, Z]]
branch = ['tr', E(V(0), Z), ['succ', Z, Z, V(1)],
          ['qe', S(Z), ['hyp', 0], ['zero', Z, V(1)]]]
escape = certificate(1, [], E(V(0), Z), ['de', E(V(0), Z), major, branch])
(outdir / 'eigenvariable_escape_rejected.json').write_text(json.dumps(escape, indent=2)+'\n')
for module in (old, new):
    if module.derive(major, [], 1) != D(gated_matrix):
        raise RuntimeError('escape control major is not valid')
    if module.derive(branch, [Q(gated_matrix)], 2) != E(V(0), Z):
        raise RuntimeError('escape control branch is not valid')
    try:
        module.check(escape)
    except (ValueError, TypeError, IndexError, KeyError):
        pass
    else:
        raise RuntimeError('fresh witness escaped to retained parameter')

receipt = dict(
    status='all targeted tests passed',
    source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (PACKAGE/'code').glob('*.py')
                  if p.name in ('strict_q.py', 'strict_old.py', 'translate.py')},
    positive_source_proofs=len(cases),
    destination_and_roundtrip_checks=2*len(cases),
    cli_runs=cli_runs,
    targeted_negative_controls=2,
    records=receipts,
    scope='Finite regression evidence; the audit also reviews the universal scoping invariants.',
)
(ROOT/'evidence/strict_review_checks.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
