"""Build and independently replay substantive certificate examples."""
from pathlib import Path
import importlib.util
import json
import sys
import copy

import macros as m
import reference_kernel as ref
from convert import certificate_to_selected, certificate_from_selected

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


forward = load('target_forward', HERE / 'forward_kernel.py')
selected = load('target_selected', ROOT / 'code/checker.py')
accepted = {}
notes = {}


def add(name, certificate, description):
    ref.check(certificate)
    forward.check(certificate)
    compact = certificate_to_selected(certificate)
    selected.check(compact)
    roundtrip = certificate_from_selected(compact)
    forward.check(roundtrip)
    if roundtrip['goal'] != certificate['goal']:
        raise ValueError('goal changed')
    accepted[name] = (certificate, compact)
    notes[name] = description
    print('PASS', name, len(json.dumps(compact)), flush=True)


for number in range(3):
    t = m.numeral(number)
    add('reflexivity_' + str(number), {'goal': [t, t], 'proof': m.refl(t)},
        'Explicit initial reflexivity axiom instantiated at a numeral.')

truth = m.D([0, 0])
major = ['i', truth, m.ONE, m.refl(0)]
ordinary = ['e', [0, 0], major, m.refl(-1), m.refl(0)]
add('ordinary_elimination_self_target', {'goal': [0, 0], 'proof': ordinary},
    'Ordinary elimination uses target equal to the newly opened parameter.')

add('symmetry_from_assumption',
    m.implication_equations([0, m.ONE], [m.ONE, 0],
                            lambda p, g, n: m.symmetry(p, g, n)),
    'Uses an assumed 0=1; recovers 1=0 through the explicit two-row name packet.')

add('successor_congruence',
    m.implication_equations([0, m.ONE], [m.ONE, m.TWO],
                            lambda p, g, n: m.congruence(p, m.S(m.V), m.V, g, n)),
    'Congruence is recovered from witness elimination, not a primitive equality rule.')

add('transitivity_uses_two_equalities',
    m.implication_equations([0, m.ONE], [0, m.TWO],
        lambda p, g, n: m.transitivity(p, m.congruence(p, m.S(m.V), m.V, g, n), g, n)),
    'Combines assumed 0=1 with independently derived 1=2 to obtain 0=2.')

repeated = m.I(m.V, m.V, m.U, m.S(m.U))
add('repeated_template_occurrences',
    m.implication_equations([0, m.ONE], [0, m.TWO],
        lambda p, g, n: m.congruence(p, repeated, m.V, g, n)),
    'Both counter and initializer contain the template variable.')

passive = m.I(m.V, m.ONE, m.U, m.S(m.U))
add('passive_source_occurrence',
    m.implication_equations([m.ONE, m.TWO], [m.TWO, m.numeral(3)],
        lambda p, g, n: m.congruence(p, passive, m.V, g, n)),
    'The source numeral1 also appears as a passive initializer and must stay unchanged.')

nested = m.I(m.Y, 0, m.U, m.I(m.V, m.U, m.W, m.S(m.W)))
nested_equation = [m.at(nested, m.V, 0), m.at(nested, m.V, m.ONE)]
add('nested_iterator_binders',
    m.implication_quantified_equation([0, m.ONE], nested_equation, m.Y,
        lambda p, y, g, n: m.congruence(p, m.at(nested, m.Y, y), m.V, g, n)),
    'A nontrivial universal step has two iterator state binders and a passive parameter.')

identity_iterator = m.I(m.Y, 0, m.U, m.S(m.U))
induction_goal = m.D([identity_iterator, m.Y])
step_eq = m.opening(m.opening(induction_goal[0], 0, 1), -1)
context = [(m.H, step_eq)]
step = m.congruence(m.hypothesis(0), m.S(m.V), m.V, context, 1)
induction = ['i', induction_goal, 0, step]
add('equation_induction_uses_hypothesis', {'goal': induction_goal, 'proof': induction},
    'Proves I(y,0;u.Su)=y. The progress branch actually consumes its induction hypothesis.')

case_goal = m.D([m.C(m.Y, 0, m.X), m.ONE])
repaired = m.repaired_zero_case(case_goal,
                               lambda z, base, g, n: base, [], 0)
add('zero_witness_case_repair_consumes_base', {'goal': case_goal, 'proof': repaired},
    'Repairs case introduction at0 using a fresh alias and consumes base0=1; the direct progress hypothesis has a different formula.')

packet, packet_proof = m.alias_zero([], 0)
fresh = -1
body = m.opening(packet[0], fresh, 1)
context = [(m.opening(body, 0), body)]
bound_term = m.I(m.Y, fresh, m.U, m.I(fresh, m.U, m.W, m.S(m.W)))
inside = m.D([bound_term, bound_term])
compound = m.D(inside, m.V, m.W)
branch = m.formula_identity(compound, context, 1)
exported = m.at(compound, fresh, 0)
fused = ['e', exported, packet_proof, m.use(0, m.ONE, m.refl(0)), branch]
add('nested_formula_substitution', {'goal': exported, 'proof': fused},
    'Substitution occurs under two D binders and iterator binders; replacing b by0 exposes computation redexes.')

# A genuinely open equality test preserves a passive occurrence of its source
# parameter. This is a local sequent test, deliberately separate from CLI files.
open_context = [(m.H, [-1, -2])]
open_template = m.I(m.V, -1, m.U, m.S(m.U))
open_proof = m.congruence(m.hypothesis(0), open_template, m.V, open_context, 2)
open_goal = [m.at(open_template, m.V, -1), m.at(open_template, m.V, -2)]
if ref.derive(open_proof, open_context, 2) != open_goal:
    raise ValueError('open sequent replay')
if forward.derive(open_proof, open_context, 2) != open_goal:
    raise ValueError('open sequent target')

out_forward = HERE / 'examples_four'
out_selected = HERE / 'examples'
out_forward.mkdir(exist_ok=True)
out_selected.mkdir(exist_ok=True)
for name, (raw, compact) in accepted.items():
    (out_forward / (name + '.json')).write_text(json.dumps(raw, indent=2) + '\n')
    (out_selected / (name + '.json')).write_text(json.dumps(compact, indent=2) + '\n')
(HERE / 'open_parameter_sequent.json').write_text(json.dumps(
    {'scope': 2, 'context': open_context, 'goal': open_goal, 'proof': open_proof}, indent=2) + '\n')
(HERE / 'positive_index.json').write_text(json.dumps(
    [{'name': name, 'description': notes[name]} for name in accepted], indent=2) + '\n')
print('TOTAL', len(accepted), 'closed examples; one independently replayed open sequent')
