"""Focused scope and recurrence tests for two complete standalone kernels.

This driver is untrusted and is not imported by either checker.  Positive
examples use literal expected conclusions; adversarial examples target the
fresh recurrence variable, absence of a local induction hypothesis, and
counter-independent update syntax.
"""
from copy import deepcopy
from pathlib import Path
import json
import subprocess
import sys


ROOT = Path(__file__).parent
Z = ['z']
V = lambda i: ['v', i]
S = lambda a: ['s', a]
I = lambda n, a, h: ['i', n, a, h]
E = lambda a, b: ['=', a, b]


def refl(a):
    p = ['zero', a, V(0)]
    return ['tr', V(0), p, p]


def sym(a, p):
    return ['tr', V(0), refl(a), p]


def certificate(n, goal, proof, context=None):
    return {'variables': n, 'context': context or [],
            'goal': goal, 'proof': proof}


cases = []


def add(name, checker, value, accepted):
    cases.append((name, checker, value, accepted))


for checker in ('baseline_qi.py', 'scalar_ur.py'):
    add('zero_computation', checker,
        certificate(1, E(I(Z, V(0), S(V(0))), V(0)),
                    ['zero', V(0), S(V(0))]), True)
    add('crossed_reflexivity', checker,
        certificate(1, E(V(0), V(0)), refl(V(0))), True)
    # Case introduction at a genuinely used existential witness, followed
    # by an elimination whose conclusion cannot contain that witness.
    matrix = E(V(1), V(1))
    paired = ['d', matrix]
    intro = ['di', matrix, Z, refl(Z)]
    add('case_introduction', checker,
        certificate(0, paired, intro), True)
    # In the DE continuation b is index 0, and Q_y(b=b) is retained.
    opened = E(V(0), V(0))
    qe = ['qe', Z, ['hyp', 0], refl(V(0))]
    add('qe_inside_de', checker,
        certificate(0, E(Z, Z),
                    ['de', E(Z, Z), intro,
                     ['tr', Z, qe, refl(Z)]]), True)
    leak = certificate(0, E(V(0), V(0)),
                       ['de', E(V(0), V(0)), intro, refl(V(0))])
    add('de_eigenvariable_escape', checker, leak, False)
    add('boolean_variable_count', checker,
        certificate(True, E(Z, Z), refl(Z)), False)
    add('boolean_variable_index', checker,
        certificate(1, E(V(True), V(True)), ['hyp', 0],
                    [E(V(0), V(0))]), False)
    add('missing_proof', checker,
        {'variables': 0, 'context': [], 'goal': E(Z, Z)}, False)
    add('false_closed_goal', checker,
        certificate(0, E(Z, S(Z)), refl(Z)), False)

# The baseline equation induction really uses its local induction hypothesis.
e = E(I(V(0), V(1), V(0)), V(1))
left = I(S(V(0)), V(1), V(0))
step = ['succ', V(0), V(1), V(0)]
progress = ['tr', V(0), ['hyp', 0], sym(left, step)]
add('qi_uses_induction_hypothesis', 'baseline_qi.py',
    certificate(1, ['q', e], ['qi', e, progress]), True)
add('qi_forbidden_at_compound', 'baseline_qi.py',
    certificate(0, ['q', ['q', E(Z, Z)]],
                ['qi', ['q', E(Z, Z)], ['hyp', 0]]), False)

# UR: f(z)=z and h(u)=S(u).  No induction hypothesis is retained.
identity = certificate(1, E(V(0), I(V(0), Z, S(V(0)))),
                       ['ur', V(0), S(V(0)), V(0), refl(S(V(0)))])
add('ur_identity_at_parameter', 'scalar_ur.py', identity, True)
add('ur_identity_at_closed_numeral', 'scalar_ur.py',
    certificate(0, E(S(S(Z)), I(S(S(Z)), Z, S(V(0)))),
                ['ur', V(0), S(V(0)), S(S(Z)), refl(S(V(0)))]), True)

# UR: f(z)=a and h(u)=u; a is passive, not the recurrence variable.
constant = certificate(2, E(V(0), I(V(1), V(0), V(0))),
                       ['ur', V(1), V(0), V(1), refl(V(1))])
add('ur_constant_orbit', 'scalar_ur.py', constant, True)

# A retained equation is shifted correctly, and supplies the whole recurrence.
contextual = certificate(2, E(V(0), I(V(0), V(0), V(2))),
                         ['ur', V(1), V(2), V(0), ['hyp', 0]],
                         [E(V(0), V(1))])
add('ur_retains_context_without_hypothesis', 'scalar_ur.py', contextual, True)

# f(z)=I(z,a;u.I(u,a;v.S(v))).  The nested body binds its own state;
# the outer update does not see the recurrence variable.
h = I(V(0), V(1), S(V(0)))
lifted_h = I(V(0), V(2), S(V(0)))
f = I(V(0), V(1), lifted_h)
target = V(0)
fz = I(Z, V(0), h)
ft = I(target, V(0), h)
nested = certificate(1, E(ft, I(target, fz, h)),
                     ['ur', f, h, target,
                      ['succ', V(0), V(1), lifted_h]])
add('ur_nested_iterator_scope', 'scalar_ur.py', nested, True)

bad = deepcopy(identity)
bad['proof'][-1] = ['hyp', 0]
add('ur_has_no_induction_hypothesis', 'scalar_ur.py', bad, False)
bad = deepcopy(identity)
bad['proof'][3] = V(1)
add('ur_target_cannot_capture_fresh_variable', 'scalar_ur.py', bad, False)
bad = deepcopy(identity)
bad['proof'][2] = V(2)
add('ur_update_cannot_add_a_counter_coordinate', 'scalar_ur.py', bad, False)
bad = deepcopy(identity)
bad['proof'][-1] = refl(V(0))
add('ur_wrong_recurrence', 'scalar_ur.py', bad, False)
bad = deepcopy(contextual)
bad['context'] = [E(V(1), V(0))]
add('ur_context_orientation_matters', 'scalar_ur.py', bad, False)
bad = deepcopy(nested)
bad['proof'][-1][-1] = h
add('ur_nested_passive_parameter_capture', 'scalar_ur.py', bad, False)
bad = deepcopy(identity)
bad['proof'][1] = ['q', E(Z, Z)]
add('ur_template_must_be_a_term', 'scalar_ur.py', bad, False)
add('old_progress_tag_removed', 'scalar_ur.py',
    certificate(1, ['q', e], ['qi', e, progress]), False)

out = ROOT / 'examples'
out.mkdir(exist_ok=True)
records = []
for name, checker, value, accepted in cases:
    file = out / (checker[:-3] + '_' + name + '.json')
    data = json.dumps(value, separators=(',', ':')) + '\n'
    file.write_text(data)
    for optimized in (False, True):
        command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / checker)]
        result = subprocess.run(command, input=data, text=True,
                                capture_output=True, timeout=15)
        actual = result.returncode == 0 and result.stdout == 'ACCEPT\n'
        record = {'case': name, 'checker': checker, 'optimized': optimized,
                  'expected_accept': accepted, 'accepted': actual,
                  'exit': result.returncode}
        if actual != accepted:
            record['stdout'] = result.stdout
            record['stderr'] = result.stderr
        records.append(record)
failures = [r for r in records if r['expected_accept'] != r['accepted']]
summary = {'process_checks': len(records),
           'expected_acceptances': sum(r['expected_accept'] for r in records),
           'expected_rejections': sum(not r['expected_accept'] for r in records),
           'mismatches': len(failures), 'results': records}
(ROOT / 'validation.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
for failure in failures:
    print(json.dumps(failure, indent=2))
sys.exit(bool(failures))
