"""Finite examples of the head-checker positivity reduction.

This is an experiment supporting a separately proved reduction, not a proof
that a procedure is or is not primitive recursive. It imports no checker as
an oracle: every verdict below comes from the standalone control subprocess.
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
Z = ['z']
V = lambda i: ['v', i]
S = lambda t: ['s', t]
I = lambda n, a, h: ['i', n, a, h]
E = lambda a, b: ['=', a, b]


def value(term, environment=()):
    """Independent standard-natural evaluator, used only for small examples."""
    tag = term[0]
    if tag == 'z':
        return 0
    if tag == 'v':
        return environment[term[1]]
    if tag == 's':
        return value(term[1], environment) + 1
    if tag == 'i':
        counter = value(term[1], environment)
        state = value(term[2], environment)
        for _ in range(counter):
            state = value(term[3], (state,) + environment)
        return state
    raise ValueError('Invalid numerical term')


# y is bound by the outer Q, and the iterator bodies are constants.
B = E(I(V(0), Z, Z), I(V(0), Z, S(Z)))
GOAL = E(Z, S(Z))
CONTEXT = [['q', B]]
assert GOAL not in CONTEXT and GOAL[1] != GOAL[2]


def payload(term):
    return dict(variables=0, context=CONTEXT, goal=GOAL,
                proof=['qe', B, term, None, None])


terms = [
    ('zero', Z),
    ('one', S(Z)),
    ('two', S(S(Z))),
    ('zero_counter_zero_seed', I(Z, Z, S(V(0)))),
    ('zero_counter_one_seed', I(Z, S(Z), S(V(0)))),
    ('one_increment', I(S(Z), Z, S(V(0)))),
    ('constant_zero_update', I(S(S(Z)), S(Z), Z)),
    ('identity_zero_state', I(S(S(Z)), Z, V(0))),
    ('identity_one_state', I(S(S(Z)), S(Z), V(0))),
    ('nested_increment_counter', I(I(S(S(Z)), Z, S(V(0))), Z, S(V(0)))),
    ('nested_counter_zero_update', I(I(S(S(Z)), Z, S(V(0))), Z, Z)),
    ('nested_body_increment', I(S(S(Z)), Z, I(S(Z), V(0), S(V(0))))),
]

results = []
for name, term in terms:
    numeric_value = value(term)
    data = payload(term)
    for optimized in (False, True):
        command = [sys.executable, '-I', '-S', '-B']
        if optimized:
            command.append('-O')
        process = subprocess.run(command + [str(ROOT / 'control.py')],
                                 input=json.dumps(data).encode(),
                                 capture_output=True, timeout=30)
        accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
        results.append(dict(name=name, term=term, numeric_value=numeric_value,
                            positive=numeric_value > 0, optimized=optimized,
                            accepted=accepted, passed=accepted == (numeric_value > 0)))

report = dict(python=sys.version, checker='control.py',
              fixed_context=CONTEXT, fixed_goal=GOAL,
              fixed_proof_skeleton=['qe', B, '<closed raw term t>', None, None],
              initial_goal_is_neither_hypothesis_nor_reflexive=True,
              statement='On these examples, acceptance is equivalent to the standard value of t being positive.',
              universal_claim_scope='The universal reduction and non-primitive-recursiveness argument require the separate written proof; finite tests do not establish either.',
              term_count=len(terms), executions=len(results),
              failed_expectations=sum(not r['passed'] for r in results),
              results=results)
output = ROOT.parent / 'evidence/normalization_boundary.json'
output.parent.mkdir(exist_ok=True)
output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
if report['failed_expectations']:
    raise SystemExit(1)
