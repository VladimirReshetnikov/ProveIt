"""Generate substantive closed and open examples and adversarial controls."""
from pathlib import Path
import copy
import json

import macros as m
from translate import candidate, control, translate_checked, to_old, old_to_independent
from inherited_reference_kernel import derive as replay_derive

ROOT = Path(__file__).resolve().parent.parent
G = [([], [1, 1])]
positives = {}
negatives = {}
notes = {}


def document(theorem):
    return {'goal': theorem.goal, 'proof': theorem.proof}


def add(name, data, description):
    translated = translate_checked(data)
    positives[name] = data
    notes[name] = description
    (ROOT / 'examples/translated_witness_discharge' / (name + '.json')).write_text(
        json.dumps(translated, indent=2) + '\n')


def reject(name, data, description):
    try:
        candidate.check(data)
    except Exception:
        negatives[name] = data
        notes[name] = description
        return
    raise ValueError('negative fixture accepted: ' + name)


for number in range(3):
    add('reflexivity_' + str(number), document(m.refl(m.numeral(number))),
        'Fixed universal reflexivity clause instantiated at a numeral.')

truth = m.D(m.H)
truth_proof = m.introduce(truth, m.ONE, lambda z, g, n, expected: m.refl(0), G, 0)
ordinary = m.eliminate(truth_proof, lambda b, g, n: m.refl(0), G, 0)
add('ordinary_open_default_wrong_left', document(ordinary),
    'Default export: base is 0=0 but row 1 has literal zero rather than the fresh witness on its left.')

alias = m.alias_zero(G, 0)
alias_open = m.eliminate(alias, lambda b, g, n: m.refl(0), G, 0)
add('ordinary_open_despite_extraction', document(alias_open),
    'The row forces replacement b->0, but a witness-free branch result still gives ordinary elimination.')

wrong_base_goal = m.D([m.C(m.Y, m.ONE, m.X), m.ONE])
wrong_base_major = m.introduce(wrong_base_goal, m.ONE,
                               lambda z, g, n, expected: m.refl(m.ONE), G, 0)
wrong_base_open = m.eliminate(wrong_base_major, lambda b, g, n: m.refl(0), G, 0)
add('ordinary_open_default_wrong_base', document(wrong_base_open),
    'Row 1 is b=1, but the base is 1=1; the exact syntactic 0=0 test forces the default mode.')

self_target = m.C(m.X, 0, m.X)
self_goal = m.D([m.C(m.Y, 0, m.X), m.C(m.Y, 0, self_target)])
self_major = m.introduce(self_goal, m.ONE,
                         lambda z, g, n, expected: m.refl(m.ONE), G, 0)
self_open = m.eliminate(self_major, lambda b, g, n: m.refl(0), G, 0)
add('extracted_target_contains_witness', document(self_open),
    'Extracts b=C(b,0,b), whose right side still contains b. A witness-free branch is legally exported; an occurs check would wrongly reject.')

add('symmetry_from_assumption',
    m.implication([0, m.ONE], [m.ONE, 0], lambda p, g, n: m.symmetry(p, g, n)),
    'Reconstructs symmetry using the first-row naming package under an actual equation assumption.')
add('successor_congruence',
    m.implication([0, m.ONE], [m.ONE, m.TWO],
                  lambda p, g, n: m.congruence(p, m.S(m.V), m.V, g, n)),
    'Reconstructs successor congruence; no primitive equality or transport instruction is used.')
add('transitivity_uses_two_equalities',
    m.implication([0, m.ONE], [0, m.TWO],
                  lambda p, g, n: m.transitivity(p, m.congruence(p, m.S(m.V), m.V, g, n), g, n)),
    'Uses the assumed 0=1 and derived 1=2 as separate premises of derived transitivity.')

repeated = m.I(m.V, m.V, m.U, m.S(m.U))
add('repeated_template_occurrences',
    m.implication([0, m.ONE], [0, m.TWO],
                  lambda p, g, n: m.congruence(p, repeated, m.V, g, n)),
    'The transport parameter occurs in both the counter and initializer.')
passive = m.I(m.V, m.ONE, m.U, m.S(m.U))
add('passive_source_occurrence',
    m.implication([m.ONE, m.TWO], [m.TWO, m.numeral(3)],
                  lambda p, g, n: m.congruence(p, passive, m.V, g, n)),
    'The numerical source 1 is also a passive initializer; replacing the fresh alias must preserve it.')

nested_template = m.I(m.Y, 0, m.U, m.I(m.V, m.U, m.W, m.S(m.W)))
nested_equation = [m.at(nested_template, m.V, 0), m.at(nested_template, m.V, m.ONE)]
nested_goal = m.D([m.C(m.Y, 0, nested_equation[0]),
                   m.C(m.Y, m.ONE, nested_equation[1])])
def nested_step(z, context, scope, expected):
    template = m.at(nested_template, m.Y, m.S(z))
    return m.congruence(m.hypothesis(1, context, scope), template, m.V, context, scope)
nested = m.introduce(nested_goal, m.ONE, nested_step, G, 0)
add('nested_iterator_congruence', document(nested),
    'Congruence under two iterator-state binders with a live universally quantified parameter.')

iterator = m.I(m.Y, 0, m.U, m.S(m.U))
induction_goal = m.D([iterator, m.Y])
induction = m.introduce(induction_goal, 0,
                        lambda z, g, n, expected: m.congruence(m.hypothesis(1, g, n),
                                                              m.S(m.V), m.V, g, n), G, 0)
add('equation_induction_uses_hypothesis', document(induction),
    'The progress branch genuinely uses its induction hypothesis to prove I(y,0;u.Su)=y.')

case_goal = m.D([m.C(m.Y, 0, m.X), m.ONE])
def repair_branch(b, local, scope):
    bzero = m.use(1, m.ONE, m.refl(0), local, scope)
    def step(z, extended, next_scope, expected):
        named = m.weaken(bzero, scope, len(local))
        return m.transitivity(named, m.hypothesis(len(local), extended, next_scope), extended, next_scope)
    return m.introduce(case_goal, b, step, local, scope)
repaired = m.eliminate(alias, repair_branch, G, 0)
add('zero_witness_case_repair', document(repaired),
    'A fresh alias repairs atomic case introduction at zero and consumes the base assumption 0=1.')

def nested_formula_branch(b, context, scope):
    term = m.I(m.Y, b, m.U, m.I(b, m.U, m.W, m.S(m.W)))
    inner = m.D([term, term])
    formula = m.D(inner, m.V, m.W)
    return m.formula_identity(formula, context, scope)
compound = m.eliminate(alias, nested_formula_branch, G, 0)
add('nested_formula_substitution', document(compound),
    'Exports through two D binders and nested iterator bodies; b->0 creates computation redexes that must normalize capture freely.')

compound_major_goal = m.D(truth)
compound_major = m.formula_identity(compound_major_goal, G, 0)
compound_open = m.eliminate(compound_major, lambda b, g, n: m.formula_identity(truth, g, n), G, 0)
add('compound_matrix_default_open', document(compound_open),
    'A D-rooted matrix cannot supply an equation row; ordinary elimination still works.')

# A local sequent with genuinely distinct free parameters. The public CLI
# deliberately accepts only closed goals, so this is recorded separately.
open_context = G + [([], [-1, -2])]
open_template = m.I(m.V, -1, m.U, m.S(m.U))
open_theorem = m.congruence(m.hypothesis(1, open_context, 2), open_template, m.V, open_context, 2)
m.check_theorem(open_theorem, open_context, 2)
old_open = to_old(open_theorem.goal, open_theorem.proof, open_context, 2)
control.prove(open_theorem.goal, old_open, open_context, 2)
replay_context = [(m.H if not base else base, body) for base, body in open_context[1:]]
replayed = replay_derive(old_to_independent(open_theorem.goal, old_open, open_context, 2), replay_context, 2)
m.ensure(replayed == open_theorem.goal, 'open independent replay failed')
open_data = {'scope': 2, 'context': open_context, 'goal': open_theorem.goal, 'proof': open_theorem.proof}
(ROOT / 'validation/open_parameter_sequent.json').write_text(json.dumps(open_data, indent=2) + '\n')

# Essential left-side guard attack. Correct checker leaves b in F; deleting
# row[0]==b exports the false closed equality 1=0.
z_x = m.C(m.X, m.ONE, 0)
attack_matrix = [m.C(m.Y, 0, m.C(m.parity(m.Y), z_x, 0)),
                 m.C(m.Y, 0, m.C(m.parity(m.Y), 0, 0))]
attack_goal = m.D(attack_matrix)
attack_major = m.introduce(attack_goal, m.ONE,
                          lambda z, g, n, expected: m.refl(expected[0]), G, 0)
body, base, target, extracted = __import__('translate').selection(attack_goal[0], 0)
local = G + [(base, body)]
attack_branch = m.use(1, m.TWO, m.refl(0), local, 1)
left_attack = {'goal': [m.ONE, 0],
               'proof': ['e', attack_goal[0], attack_branch.goal, attack_major.proof, attack_branch.proof]}
reject('essential_left_guard_false_equality', left_attack,
       'Deleting the left-witness test accepts false 1=0: row 1 is 0=0 and row 2 is Z(b)=0.')

# Essential base guard attack. The opened clause has antecedent b=0 and
# row 1 b=0. Its conditional closure is derivable, but may not be exported
# at b=0. Deleting the base==0=0 test makes a false closure provable.
base_attack_matrix = [m.C(m.Y, m.X, m.C(m.parity(m.Y), m.ONE, m.X)), 0]
base_attack_goal = m.D(base_attack_matrix)
def base_attack_step(z, context, scope, expected):
    premise = m.hypothesis(1, context, scope)
    template = [m.C(m.V, m.ONE, m.ONE), 0]
    def successor(zz, extended, next_scope):
        return m.weaken(premise, scope, len(context))
    return m.numerical_cases(template, m.V, m.parity(m.S(z)), premise, successor, context, scope)
base_attack_major = m.introduce(base_attack_goal, m.ONE, base_attack_step, G, 0)
body, base, target, extracted = __import__('translate').selection(base_attack_goal[0], 0)
local = G + [(base, body)]
named_matrix = m.opening(body, m.Y)
local_closure_goal = m.D(named_matrix, m.W, m.Y)
def close_local(z, extended, next_scope, expected):
    return m.use(1, m.S(z), m.hypothesis(len(local), extended, next_scope), extended, next_scope)
base_attack_branch = m.introduce(local_closure_goal, m.ONE, close_local, local, 1)
false_closure = m.at(base_attack_branch.goal, -1, 0)
base_attack = {'goal': false_closure,
               'proof': ['e', base_attack_goal[0], base_attack_branch.goal,
                         base_attack_major.proof, base_attack_branch.proof]}
reject('essential_base_guard_false_closure', base_attack,
       'Deleting the exact base test exports a closure whose base is true and whose second row is 1=0.')

escape = {'goal': m.H, 'proof': ['e', truth[0], [-1, -1], truth_proof.proof, m.refl(-1).proof]}
reject('default_eigenvariable_escape', escape,
       'The default mode cannot erase a fresh witness from a reflexive branch equation.')
scope_attack = copy.deepcopy(escape)
scope_attack['goal'] = [-1, -1]
reject('outer_scope_guard_escape', scope_attack,
       'Removing current-goal scope validation accepts a free eigenparameter in the purported closed conclusion.')

reject('false_equality', {'goal': [0, m.ONE], 'proof': m.refl(0).proof}, 'Rejects 0=1.')
reject('wrong_clause_antecedent',
       {'goal': m.H, 'proof': ['e', alias.goal[0], [-1, 0], alias.proof, ['u', 1, m.ONE, m.refl(m.ONE).proof]]},
       'The extracted equality is not free-standing: clause use must supply the actual 0=0 antecedent.')
reject('old_explicit_packet_not_accepted', translate_checked(positives['ordinary_open_despite_extraction']),
       'The old seven-field E packet is not a deterministic-discharge certificate.')
reject('invalid_major', {'goal': m.H, 'proof': ['e', truth[0], m.H, m.refl(0).proof, m.refl(0).proof]},
       'An equation proof cannot serve as a D major.')
reject('invalid_branch', {'goal': m.H, 'proof': ['e', truth[0], m.H, truth_proof.proof, m.refl(m.ONE).proof]},
       'The branch must prove its declared formula before export.')
reject('negative_clause_index', {'goal': m.H, 'proof': ['u', -1, 0, None]}, 'Negative context indices are rejected.')
reject('boolean_clause_index', {'goal': m.H, 'proof': ['u', False, 0, None]}, 'Booleans are not clause indices.')
reject('boolean_term', {'goal': m.H, 'proof': ['u', 0, False, None]}, 'Booleans are not numerical terms.')
reject('string_term', {'goal': m.H, 'proof': ['u', 0, '0', None]}, 'Strings are not numerical terms.')
reject('extra_proof_field', {'goal': m.H, 'proof': ['u', 0, 0, None, None]}, 'Exact packet arity is checked.')
reject('extra_document_field', {'goal': m.H, 'proof': m.refl(0).proof, 'extra': 1}, 'Exact public key set is checked.')
reject('empty_proof', {'goal': m.H, 'proof': []}, 'Missing proof instruction is rejected.')
reject('loose_bound_variable', {'goal': [1, 1], 'proof': ['u', 0, 1, None]}, 'A bound variable cannot escape to the outer scope.')
reject('malformed_formula', {'goal': [], 'proof': m.refl(0).proof}, 'Empty formulas are rejected.')
reject('noncanonical_zero_iterator', {'goal': [[0, 0, 1], 0], 'proof': m.refl(0).proof}, 'Goals must already be full normal forms.')
capture = copy.deepcopy(positives['nested_formula_substitution'])
capture['goal'] = m.D(m.D([3, 3]))
reject('nested_binder_capture_mismatch', capture,
       'An unrelated bound-coordinate result cannot replace the capture-avoiding normalized export.')

for name, data in positives.items():
    (ROOT / 'examples/positive' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
for name, data in negatives.items():
    (ROOT / 'examples/negative' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
(ROOT / 'evidence/fixture_index.json').write_text(json.dumps(
    [{'name': name, 'expected': 'ACCEPT' if name in positives else 'REJECT', 'description': description}
     for name, description in notes.items()], indent=2) + '\n')
print(json.dumps({'positive': len(positives), 'negative': len(negatives), 'open_local_sequents': 1}))
