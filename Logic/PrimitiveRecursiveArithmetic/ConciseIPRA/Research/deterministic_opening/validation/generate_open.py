"""Generate opening certificates and matched old proofs of the same theorems.

This is deliberately not a generic executable translation out of the new
opening calculus. Both certificate families are produced by corresponding
explicit mathematical constructions. The old family is independently replayed.
"""
from pathlib import Path
import copy
import json

import macros as dd
import macros_open as oo
from translate import translate_checked, to_old, old_to_independent, control, selection
from inherited_reference_kernel import derive as replay_derive

ROOT = Path(__file__).resolve().parent.parent
for folder in ['examples_open/positive', 'examples_open/negative', 'examples_open/matched_old_proofs']:
    (ROOT / folder).mkdir(parents=True, exist_ok=True)


def doc(theorem):
    return {'goal': theorem.goal, 'proof': theorem.proof}


def build(module):
    m = module
    g0 = [([], [1, 1])]
    result = {}
    for number in range(3):
        result['reflexivity_' + str(number)] = doc(m.refl(m.numeral(number)))
    truth = m.D(m.H)
    major = m.introduce(truth, m.ONE, lambda z, g, n, e: m.refl(0), g0, 0)
    result['ordinary_open_default_wrong_left'] = doc(m.eliminate(major, lambda b, g, n: m.refl(0), g0, 0))
    alias = m.alias_zero(g0, 0)
    result['ordinary_open_despite_extraction'] = doc(m.eliminate(alias, lambda b, g, n: m.refl(0), g0, 0))
    base_goal = m.D([m.C(m.Y, m.ONE, m.X), m.ONE])
    base_major = m.introduce(base_goal, m.ONE, lambda z, g, n, e: m.refl(m.ONE), g0, 0)
    result['ordinary_open_default_wrong_base'] = doc(m.eliminate(base_major, lambda b, g, n: m.refl(0), g0, 0))
    self_target = m.C(m.X, 0, m.X)
    self_goal = m.D([m.C(m.Y, 0, m.X), m.C(m.Y, 0, self_target)])
    self_major = m.introduce(self_goal, m.ONE, lambda z, g, n, e: m.refl(m.ONE), g0, 0)
    result['extracted_target_contains_witness'] = doc(m.eliminate(self_major, lambda b, g, n: m.refl(0), g0, 0))
    result['symmetry_from_assumption'] = m.implication([0, m.ONE], [m.ONE, 0], lambda p, g, n: m.symmetry(p, g, n))
    result['successor_congruence'] = m.implication([0, m.ONE], [m.ONE, m.TWO],
                                                 lambda p, g, n: m.congruence(p, m.S(m.V), m.V, g, n))
    result['transitivity_uses_two_equalities'] = m.implication([0, m.ONE], [0, m.TWO],
            lambda p, g, n: m.transitivity(p, m.congruence(p, m.S(m.V), m.V, g, n), g, n))
    repeated = m.I(m.V, m.V, m.U, m.S(m.U))
    result['repeated_template_occurrences'] = m.implication([0, m.ONE], [0, m.TWO],
                                                          lambda p, g, n: m.congruence(p, repeated, m.V, g, n))
    passive = m.I(m.V, m.ONE, m.U, m.S(m.U))
    result['passive_source_occurrence'] = m.implication([m.ONE, m.TWO], [m.TWO, m.numeral(3)],
                                                       lambda p, g, n: m.congruence(p, passive, m.V, g, n))
    nested_template = m.I(m.Y, 0, m.U, m.I(m.V, m.U, m.W, m.S(m.W)))
    nested_eq = [m.at(nested_template, m.V, 0), m.at(nested_template, m.V, m.ONE)]
    nested_goal = m.D([m.C(m.Y, 0, nested_eq[0]), m.C(m.Y, m.ONE, nested_eq[1])])
    def nested_step(z, g, n, expected):
        return m.congruence(m.hypothesis(1, g, n), m.at(nested_template, m.Y, m.S(z)), m.V, g, n)
    result['nested_iterator_congruence'] = doc(m.introduce(nested_goal, m.ONE, nested_step, g0, 0))
    iterator = m.I(m.Y, 0, m.U, m.S(m.U))
    induction_goal = m.D([iterator, m.Y])
    result['equation_induction_uses_hypothesis'] = doc(m.introduce(induction_goal, 0,
        lambda z, g, n, e: m.congruence(m.hypothesis(1, g, n), m.S(m.V), m.V, g, n), g0, 0))
    compound_major_goal = m.D(truth)
    compound_major = m.formula_identity(compound_major_goal, g0, 0)
    result['compound_matrix_default_open'] = doc(m.eliminate(compound_major,
                                                            lambda b, g, n: m.formula_identity(truth, g, n), g0, 0))
    # The outer template contains bound state variables and repeated aliases;
    # equality is hypothetical, so two distinct endpoints really are used.
    nested_body = m.I(m.V, m.V, m.U, m.I(m.U, m.V, m.W, m.S(m.W)))
    left, right = m.at(nested_body, m.V, 0), m.at(nested_body, m.V, m.ONE)
    result['extracted_clause_normalizes_nested_iterators'] = m.implication([0, m.ONE], [left, right],
        lambda p, g, n: m.congruence(p, nested_body, m.V, g, n))
    return result


new = build(oo)
old_source = build(dd)
for name, data in new.items():
    oo.candidate.check(data)
    matched = translate_checked(old_source[name])
    if matched['goal'] != data['goal']:
        raise ValueError('matched theorem changed: ' + name)
    (ROOT / 'examples_open/positive' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    (ROOT / 'examples_open/matched_old_proofs' / (name + '.json')).write_text(json.dumps(matched, indent=2) + '\n')

# Open local sequent, checked through both interfaces. The old construction
# is independently replayed; this is not submitted to the closed-goal CLI.
open_results = []
for m in (oo, dd):
    context = [([], [1, 1]), ([], [-1, -2])]
    template = m.I(m.V, -1, m.U, m.S(m.U))
    th = m.congruence(m.hypothesis(1, context, 2), template, m.V, context, 2)
    m.check_theorem(th, context, 2)
    open_results.append(th)
if open_results[0].goal != open_results[1].goal:
    raise ValueError('open matched theorem changed')
old_open = to_old(open_results[1].goal, open_results[1].proof, context, 2)
control.prove(open_results[1].goal, old_open, context, 2)
derived = replay_derive(old_to_independent(open_results[1].goal, old_open, context, 2),
                        [(dd.H, [-1, -2])], 2)
if derived != open_results[0].goal:
    raise ValueError('open independent replay failed')
(ROOT / 'validation/opening_parameter_sequent.json').write_text(json.dumps({
    'scope': 2, 'context': context, 'goal': open_results[0].goal, 'proof': open_results[0].proof,
    'matched_old_proof': old_open}, indent=2) + '\n')

m = oo
g0 = [([], [1, 1])]
bad = {}
descriptions = {}
def reject(name, data, description):
    try:
        m.candidate.check(data)
    except Exception:
        bad[name] = data
        descriptions[name] = description
        return
    raise ValueError('negative opening fixture accepted: ' + name)

truth = m.D(m.H)
truth_proof = m.introduce(truth, m.ONE, lambda z, g, n, e: m.refl(0), g0, 0)

z_x = m.C(m.X, m.ONE, 0)
left_matrix = [m.C(m.Y, 0, m.C(m.parity(m.Y), z_x, 0)),
               m.C(m.Y, 0, m.C(m.parity(m.Y), 0, 0))]
left_goal = m.D(left_matrix)
left_major = m.introduce(left_goal, m.ONE, lambda z, g, n, e: m.refl(e[0]), g0, 0)
left_attack = {'goal': [m.ONE, 0],
               'proof': ['e', left_goal[0], left_major.proof, ['u', 1, m.TWO, m.refl(0).proof]]}
reject('essential_left_guard_false_equality', left_attack,
       'Omitting the left-witness guard opens the matrix at 0 and accepts false 1=0.')

base_matrix = [m.C(m.Y, m.X, m.C(m.parity(m.Y), m.ONE, m.X)), 0]
base_goal = m.D(base_matrix)
def base_step(z, g, n, expected):
    hyp = m.hypothesis(1, g, n)
    template = [m.C(m.V, m.ONE, m.ONE), 0]
    return m.numerical_cases(template, m.V, m.parity(m.S(z)), hyp,
                             lambda zz, extended, nn: m.weaken(hyp, n, len(g)), g, n)
base_major = m.introduce(base_goal, m.ONE, base_step, g0, 0)
base_attack = {'goal': [m.ONE, 0],
               'proof': ['e', base_goal[0], base_major.proof, ['u', 1, m.TWO, m.refl(0).proof]]}
reject('essential_base_guard_false_equality', base_attack,
       'Omitting the base-H guard opens a merely conditional witness at 0 and accepts false 1=0.')

scope_attack = {'goal': [-1, -1],
                'proof': ['e', truth[0], truth_proof.proof, m.refl(-1).proof]}
reject('outer_scope_guard_escape', scope_attack, 'An opened witness cannot escape into the outer closed goal.')
reject('false_equality', {'goal': [0, m.ONE], 'proof': m.refl(0).proof}, 'Rejects 0=1.')
reject('wrong_clause_antecedent', {'goal': m.H,
       'proof': ['e', m.alias_zero(g0, 0).goal[0], m.alias_zero(g0, 0).proof,
                 ['u', 1, m.ONE, m.refl(m.ONE).proof]]},
       'Even after automatic opening the singleton clause needs its exact antecedent proof.')
reject('old_discharge_packet', old_source['ordinary_open_despite_extraction'],
       'A five-field discharge packet is not an automatic-opening packet.')
reject('invalid_major', {'goal': m.H, 'proof': ['e', truth[0], m.refl(0).proof, m.refl(0).proof]},
       'An equation proof cannot establish a paired major.')
reject('invalid_branch', {'goal': m.H, 'proof': ['e', truth[0], truth_proof.proof, m.refl(m.ONE).proof]},
       'The branch checks the exact unchanged outer goal.')
reject('negative_clause_index', {'goal': m.H, 'proof': ['u', -1, 0, None]}, 'Negative indices are invalid.')
reject('boolean_clause_index', {'goal': m.H, 'proof': ['u', False, 0, None]}, 'Boolean indices are invalid.')
reject('boolean_term', {'goal': m.H, 'proof': ['u', 0, False, None]}, 'Booleans are not terms.')
reject('string_term', {'goal': m.H, 'proof': ['u', 0, '0', None]}, 'Strings are not terms.')
reject('extra_proof_field', {'goal': m.H, 'proof': ['u', 0, 0, None, None]}, 'Packet arity is exact.')
reject('extra_document_field', {'goal': m.H, 'proof': m.refl(0).proof, 'extra': 1}, 'Document keys are exact.')
reject('empty_proof', {'goal': m.H, 'proof': []}, 'Missing rule is rejected.')
reject('loose_bound_variable', {'goal': [1, 1], 'proof': ['u', 0, 1, None]}, 'Loose positive indices are invalid.')
reject('malformed_formula', {'goal': [], 'proof': m.refl(0).proof}, 'Empty formula is invalid.')
reject('noncanonical_zero_iterator', {'goal': [[0, 0, 1], 0], 'proof': m.refl(0).proof}, 'Goals must be normal.')
capture = copy.deepcopy(new['nested_iterator_congruence'])
capture['goal'] = m.D([3, 3])
reject('nested_binder_capture_mismatch', capture, 'An escaped binder coordinate cannot replace the intended quantified result.')

for name, data in bad.items():
    (ROOT / 'examples_open/negative' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
(ROOT / 'evidence/opening_fixture_index.json').write_text(json.dumps({
    'positive': list(new), 'negative': descriptions,
    'comparison': 'Matched independently generated old proofs of identical end theorems, not a generic executable opening-to-old translation.',
    'open_local_sequents': 1}, indent=2) + '\n')
print(json.dumps({'opening_positive': len(new), 'opening_negative': len(bad), 'matched_old_independent_replays': len(new), 'open_local_sequents': 1}))
