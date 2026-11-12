"""Untrusted proof translations and regression tests for the clausal calculus.

First-class native Q formulas are expanded to D with an unused witness.
No proof-search oracle or semantic arithmetic evaluation is used in any
acceptance implementation. This test harness is separate from the kernel.
"""
import copy
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'code'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


base = load('one_term_tests', ROOT / 'tests/verify_one_term.py')
native = base.new
cl = load('clausal', OUTPUT / 'clausal_checker.py')


def translate_formula(formula):
    if formula[0] == '=':
        return copy.deepcopy(formula)
    body = translate_formula(formula[1])
    if formula[0] == 'Q':
        body = cl.shift_formula(body, 1, 1)
    return ['D', body]


def neutral():
    return ['r', 0, 0, 0]


def constant_clause(formula):
    return (['=', [[0, 0, 0], 0, 0], 0], cl.shift_formula(formula))


def translate_context(context, kinds):
    result = []
    for formula, kind in zip(context, kinds):
        if kind == 'ordinary':
            result.append(constant_clause(translate_formula(formula)))
        else:
            assert kind == 'closure' and formula[0] == 'Q'
            body = translate_formula(formula[1])
            result.append((cl.subst_formula(body, [0]), body))
    return result


def quote_clause(body, index, context_size):
    """Turn the activated clause B(0)=>all y B(y) into unused-witness D."""
    goal = ['D', cl.shift_formula(body, 1, 1)]
    local_base = ['u', context_size, 0, neutral()]
    return ['i', goal, cl.successor(0),
            ['u', index, cl.successor(1), local_base]]


def lift_clausal(proof, insertion_index, depth=0):
    """Insert one fresh parameter and one retained clause outside a proof.

The old retained clauses keep their indices. Clauses local to the lifted
proof move one place because the new retained clause precedes all of them.
"""
    tag = proof[0]
    if tag == 'u':
        index, witness, premise = proof[1:]
        index += index >= insertion_index
        return ['u', index, cl.shift_term(witness, depth=depth),
                lift_clausal(premise, insertion_index, depth)]
    if tag == 'r':
        return ['r', cl.shift_term(proof[1], depth=depth),
                cl.shift_term(proof[2], depth=depth),
                cl.shift_term(proof[3], depth=depth + 1)]
    if tag == 'x':
        return ['x', cl.shift_term(proof[1], depth=depth + 1),
                lift_clausal(proof[2], insertion_index, depth),
                lift_clausal(proof[3], insertion_index, depth)]
    if tag in ('e', 'i'):
        data = (lift_clausal(proof[2], insertion_index, depth) if tag == 'e'
                else cl.shift_term(proof[2], depth=depth))
        return [tag, cl.shift_formula(proof[1], depth=depth), data,
                lift_clausal(proof[3], insertion_index, depth + 1)]
    raise ValueError('unknown clausal rule')


def native_to_clausal(proof, context=(), kinds=(), scope=0):
    context, kinds = list(context), list(kinds)
    goal = native.derive(proof, context, scope)
    translated_goal = translate_formula(goal)
    clause_context = translate_context(context, kinds)
    tag = proof[0]
    if tag == 'h':
        index = proof[1]
        if kinds[index] == 'ordinary':
            result = ['u', index, 0, neutral()]
        else:
            result = quote_clause(clause_context[index][1], index, len(context))
    elif tag == 'r':
        result = copy.deepcopy(proof)
    elif tag == 'x':
        result = ['x', proof[1], native_to_clausal(proof[2], context, kinds, scope),
                  native_to_clausal(proof[3], context, kinds, scope)]
    elif tag == 'q':
        major = native_to_clausal(proof[2], context, kinds, scope)
        premise = native_to_clausal(proof[3], context, kinds, scope)
        result = ['e', translated_goal, major,
                  ['u', len(context), cl.shift_term(proof[1]),
                   lift_clausal(premise, len(context))]]
    elif tag == 'e':
        paired = native.derive(proof[2], context, scope)
        extended = [native.shift_formula(a) for a in context] + [['Q', paired[1]]]
        result = ['e', translated_goal, native_to_clausal(proof[2], context, kinds, scope),
                  native_to_clausal(proof[3], extended, kinds + ['closure'], scope + 1)]
    elif tag == 'i':
        body = native.shift_formula(goal[1], 1, 2)
        witness = native.shift_term(proof[2])
        eta = 1 if goal[1][0] == '=' and proof[2] == 0 else 0
        hypothesis = native.subst_formula(body, [eta, witness])
        extended = [native.shift_formula(a) for a in context] + [hypothesis]
        result = ['i', translated_goal, proof[2],
                  native_to_clausal(proof[3], extended, kinds + ['ordinary'], scope + 1)]
    else:
        raise ValueError('unknown native rule')
    got = cl.derive(result, clause_context, scope)
    if got != translated_goal:
        raise RuntimeError(f'Native-to-clausal mismatch at {tag}: {got!r} != {translated_goal!r}')
    return result


def clausal_to_native(proof, context=(), kinds=(), scope=0):
    """Use the invariant that every generated clause is ordinary or activated."""
    context, kinds = list(context), list(kinds)
    tag = proof[0]
    if tag == 'u':
        index, witness, premise = proof[1:]
        if kinds[index] == 'ordinary':
            result = ['h', index]
        else:
            result = ['q', witness, ['h', index],
                      clausal_to_native(premise, context, kinds, scope)]
    elif tag == 'r':
        result = copy.deepcopy(proof)
    elif tag == 'x':
        result = ['x', proof[1], clausal_to_native(proof[2], context, kinds, scope),
                  clausal_to_native(proof[3], context, kinds, scope)]
    elif tag == 'e':
        major = clausal_to_native(proof[2], context, kinds, scope)
        paired = native.derive(major, context, scope)
        extended = [native.shift_formula(a) for a in context] + [['Q', paired[1]]]
        result = ['e', proof[1], major,
                  clausal_to_native(proof[3], extended, kinds + ['closure'], scope + 1)]
    elif tag == 'i':
        goal, witness = proof[1:3]
        body = native.shift_formula(goal[1], 1, 2)
        eta = 1 if goal[1][0] == '=' and witness == 0 else 0
        hypothesis = native.subst_formula(body, [eta, native.shift_term(witness)])
        extended = [native.shift_formula(a) for a in context] + [hypothesis]
        result = ['i', goal, witness,
                  clausal_to_native(proof[3], extended, kinds + ['ordinary'], scope + 1)]
    else:
        raise ValueError('unknown clausal rule')
    clauses = translate_context(context, kinds)
    got = native.derive(result, context, scope)
    expected = cl.derive(proof, clauses, scope)
    if got != expected:
        raise RuntimeError(f'Clausal-to-native mismatch at {tag}')
    return result


def negative_cases(positive):
    eq = base.eq
    S = cl.successor
    ref = positive['reflexivity_zero']['proof']
    bad = {
        'false_goal': base.packet(eq(0, S(0)), ref),
        'boolean_term': base.packet(eq(True, True), ref),
        'float_term': base.packet(eq(0.0, 0.0), ref),
        'free_goal_variable': base.packet(eq(1, 1), ref),
        'negative_goal_variable': base.packet(eq(-1, -1), ref),
        'noncanonical_goal': base.packet(eq([0, 0, 1], S(0)), ref),
        'first_class_Q_forbidden': base.packet(['Q', eq(1, 1)], ref),
        'old_hyp_rule_forbidden': base.packet(eq(0, 0), ['h', 0]),
        'old_qe_rule_forbidden': base.packet(eq(0, 0), ['q', 0, ref, ref]),
        'old_zero_rule_forbidden': base.packet(eq(S(0), S(0)), ['z', 0, 0]),
        'use_empty_context': base.packet(eq(0, 0), ['u', 0, 0, neutral()]),
        'extra_rule_field': base.packet(eq(0, 0), ['r', 0, 0, 0, 0]),
        'extra_top_level_field': dict(positive['reflexivity_zero'], oracle=True),
        'recursor_body_scope': base.packet(eq(0, 0), ['r', 0, 0, 2]),
        'term_template_scope': base.packet(eq(0, 0), ['x', 2, neutral(), ref]),
        'equation_template_forbidden': base.packet(eq(0, 0), ['x', eq(1, 1), neutral(), ref]),
        'wrong_template_instance': base.packet(eq(0, 0), ['x', S(1), neutral(), ref]),
    }
    ordinary_goal = ['D', ['D', eq(1, 1)]]
    bad['use_bad_neutral_premise'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, 0, ['u', 0, 0, ref]])
    bad['use_boolean_index'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, 0, ['u', True, 0, neutral()]])
    bad['use_negative_index'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, 0, ['u', -1, 0, neutral()]])
    bad['use_future_index'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, 0, ['u', 1, 0, neutral()]])
    bad['use_future_witness'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, 0, ['u', 0, 2, neutral()]])
    bad['intro_future_witness'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, 1, ['u', 0, 0, neutral()]])
    bad['intro_noncanonical_witness'] = base.packet(ordinary_goal,
        ['i', ordinary_goal, [0, 0, 1], ['u', 0, 0, neutral()]])
    bad['intro_equation_goal'] = base.packet(eq(0, 0),
        ['i', eq(0, 0), 0, ref])
    bad['elim_nonpaired_major'] = base.packet(eq(0, 0),
        ['e', eq(0, 0), ref, ref])
    paired = positive['progress_introduction']['proof']
    bad['elim_parameter_escape'] = base.packet(eq(0, 0),
        ['e', eq(1, 1), paired, ['u', 0, 0, neutral()]])
    return bad


def run():
    native_positive, _ = base.cases()
    inherited_positive, _ = base.controls.cases(base.old, 'canonical')
    for name, data in inherited_positive.items():
        native_positive['baseline_' + name] = base.packet(data['goal'], base.old_to_new(data['proof']))
    positive = {name: base.packet(translate_formula(data['goal']), native_to_clausal(data['proof']))
                for name, data in native_positive.items()}
    negative = negative_cases(positive)
    metrics = base.measure(OUTPUT / 'clausal_checker.py')
    paths = [OUTPUT / 'clausal_checker.py', OUTPUT / 'clausal_checker.normalized.py']
    records = []
    for expected, collection in ((True, positive), (False, negative)):
        for name, data in collection.items():
            destination = ROOT / 'evidence/clausal_certificates' / (name + '.json')
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            for path in paths:
                for optimized in (False, True):
                    base.cli(path, data, expected, optimized)
            if expected:
                translated = clausal_to_native(data['proof'])
                native.verify(base.packet(data['goal'], translated))
                base.cli(BASELINE_PATH, base.packet(data['goal'], base.new_to_old(translated)), True)
            records.append({'name': name, 'expected': 'ACCEPT' if expected else 'REJECT'})
    result = {'python': sys.version, 'metrics': metrics,
              'positive_certificates': len(positive), 'negative_certificates': len(negative),
              'candidate_cli_checks': 4 * (len(positive) + len(negative)),
              'reverse_translation_to_baseline_cli_checks': len(positive),
              'certificates': records,
              'scope': 'Finite executable checks and explicit proof translations, not proof-assistant verification.'}
    (ROOT / 'evidence/clausal_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'certificates'}, indent=2))


BASELINE_PATH = base.BASE / 'canonical_checker.py'
if __name__ == '__main__':
    run()
