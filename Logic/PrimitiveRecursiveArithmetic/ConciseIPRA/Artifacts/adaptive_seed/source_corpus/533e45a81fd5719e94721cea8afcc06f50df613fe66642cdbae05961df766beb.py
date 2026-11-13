"""Reproducible focused certificate checks; no finite test claims universal soundness."""
import copy
import json
from pathlib import Path
import subprocess
import sys

import root_seed_checker as kernel
from root_seed_producer import Producer, Eq, I, S, nodes

ROOT = Path(__file__).resolve().parent
records = []
packets = []
scoped_packets = []


def positive(label, proof, expected, context=(), scope=frozenset(), count=None):
    actual = kernel.infer(proof, context, scope)
    assert kernel.same(actual, expected), label
    if count is not None:
        assert nodes(proof) == count, (label, nodes(proof), count)
    records.append({'label': label, 'expected': 'accept', 'nodes': nodes(proof), 'passed': True})
    scoped_packets.append({'label': label, 'goal': expected, 'proof': proof,
                           'context': context, 'scope': sorted(scope)})
    if not context and not scope:
        packets.append({'label': label, 'accept': True, 'packet': [expected, proof]})


def negative(label, packet):
    try:
        kernel.verify(packet)
    except Exception:
        records.append({'label': label, 'expected': 'reject', 'passed': True})
        packets.append({'label': label, 'accept': False, 'packet': packet})
    else:
        raise AssertionError('unexpected acceptance: ' + label)


def main():
    p = Producer({'x', 'y', 'w', 'u', 'v', 'a', 'b', 'c', 'd', 'e'})
    scope = frozenset({'x', 'y'})
    context = (Eq('x', 'y'),)
    templates = [0, 'w', S('w'), I('w', 'w', 'u', S('u')),
                 I(S('w'), I(0, 'w', 'v', 0), 'u', I('u', 'w', 'v', S('v'))),
                 I('w', 0, 'u', I('u', 'w', 'v', I('v', 'w', 'w', S('w'))))]
    for index, template in enumerate(templates):
        proof = p.congruence(['hyp', 0], template, 'w', context, scope)
        expected = Eq(kernel.substitute(template, 'w', 'x'), kernel.substitute(template, 'w', 'y'))
        positive('context_congruence_' + str(index), proof, expected, context, scope, 9)

    for depth in range(7):
        template = 'w'
        for _ in range(depth):
            template = S(template)
        proof = p.congruence(['hyp', 0], template, 'w', context, scope)
        positive('constant_node_bound_depth_' + str(depth), proof,
                 Eq(kernel.substitute(template, 'w', 'x'), kernel.substitute(template, 'w', 'y')),
                 context, scope, 9)

    formula_templates = [Eq(S('w'), I(0, 'w', 'u', 0)),
                         ['Q', 'b', Eq(I('b', 'w', 'u', S('u')), 'b')],
                         ['D', 'a', 'b', Eq(I('b', 'w', 'u', S('u')), 'a')],
                         ['D', 'a', 'b', ['Q', 'c', ['D', 'd', 'e',
                          Eq(I('b', 'w', 'u', I('c', 'u', 'v', S('v'))),
                             I('e', 'd', 'u', 'a'))]]],
                         ['Q', 'y', Eq('w', 'y')],
                         ['D', 'x', 'y', Eq('w', I('y', 'x', 'u', S('u')))]]
    for index, template in enumerate(formula_templates):
        old = kernel.substitute(template, 'w', 'x')
        context2 = (Eq('x', 'y'), old)
        proof = p.transport(['hyp', 0], ['hyp', 1], template, 'w', context2, scope)
        positive('full_formula_transport_' + str(index), proof,
                 kernel.substitute(template, 'w', 'y'), context2, scope)

    for counter in (0, S(0), S(S('x'))):
        value = I(counter, 'y', 'u', S('u'))
        proof = ['comp', value]
        positive('computation_' + str(counter), proof, Eq(value, kernel.computation(value)), (), scope)

    for index, counter in enumerate((0, S(0), 'x', S('x'))):
        update = S(I('u', 'x', 'v', S('v')))
        proof = p.ordinary_successor(counter, 'x', 'u', update, (), scope)
        expected = Eq(I(S(counter), 'x', 'u', update),
                      kernel.substitute(update, 'u', I(counter, 'x', 'u', update)))
        positive('recovered_IS_with_shared_passive_parameter_' + str(index), proof, expected, (), scope)

    ordinary = p.ordinary_successor(0, S(0), 'u', S('u'))
    positive('closed_recovered_old_IS', ordinary,
             Eq(I(S(0), S(0), 'u', S('u')), S(I(0, S(0), 'u', S('u')))))

    positive('closed_reflexivity', p.refl(S(0)), Eq(S(0), S(0)))
    one = I(S(0), S(0), 'u', S('u'))
    positive('one_step_computation', ['comp', one], Eq(one, S(S(0))))
    zero = I(0, S(0), 'u', S('u'))
    equality = ['comp', zero]
    closed_template = I(S('w'), 'w', 'u', S('u'))
    congruence = p.congruence(equality, closed_template, 'w')
    positive('closed_nested_congruence', congruence,
             Eq(kernel.substitute(closed_template, 'w', zero),
                kernel.substitute(closed_template, 'w', S(0))), count=9)

    for mode in ('case', 'ind'):
        goal = ['D', 'a', 'b', Eq('b', 'b')]
        eigen = p.fresh()
        proof = ['intro', goal, 0, eigen, mode, p.refl(S(eigen))]
        positive('paired_' + mode, proof, goal)

    iteration_equation = Eq(I('b', 0, 'u', 'u'), 0)
    induction_goal = ['D', 'a', 'b', iteration_equation]
    induction_eigen = p.fresh()
    local = kernel.substitute(iteration_equation, 'b', induction_eigen)
    induction_context = (local,)
    induction_scope = frozenset({induction_eigen})
    induction_step = p.ordinary_successor(induction_eigen, 0, 'u', 'u',
                                          induction_context, induction_scope)
    induction_step = p.trans(induction_step, ['hyp', 0], induction_context, induction_scope)
    induction = ['intro', induction_goal, 0, induction_eigen, 'ind', induction_step]
    positive('genuine_progress_IH_use', induction, induction_goal)
    wrong_choice = copy.deepcopy(induction)
    wrong_choice[4] = 'case'
    negative('wrong_choice_at_genuine_progress', [induction_goal, wrong_choice])

    goal = ['D', 'a', 'b', Eq(0, S(0))]
    eigen = p.fresh()
    false_base = ['intro', goal, 0, eigen, 'case', ['hyp', 0]]
    positive('case_retains_false_base', false_base, goal)

    negative('wrong_one_step_result', [Eq(one, S(0)), ['comp', one]])
    negative('zero_computation_wrong_result', [Eq(zero, 0), ['comp', zero]])
    negative('ordinary_step_not_a_primitive',
             [Eq(I(S(0), 0, 'u', S('u')), S(I(0, 0, 'u', S('u')))),
              ['comp', I(S(0), 0, 'u', S('u'))]])
    negative('free_variable_in_closed_goal', [Eq('x', 'x'), ['hyp', 0]])
    negative('negative_hypothesis_index', [Eq(0, 0), ['hyp', -1]])
    negative('Boolean_hypothesis_index', [Eq(0, 0), ['hyp', False]])
    negative('bad_term_arity', [Eq(['S', 0, 0], 0), ['comp', zero]])
    negative('unknown_term_operator', [Eq(['eval', 0], 0), ['comp', zero]])
    negative('unknown_rule', [Eq(0, 0), ['oracle']])
    negative('extra_proof_fields', [Eq(0, 0), ['hyp', 0, 0]])
    negative('wrong_root_source', [Eq(0, 0), ['root', ['comp', zero], p.refl(0)]])
    negative('seed_rule_on_successor', [Eq(S(S(0)), S(S(0))),
                                       ['seed', ['comp', zero], p.refl(S(S(0)))]])
    compound = ['D', 'a', 'b', ['D', 'c', 'd', Eq(0, 0)]]
    negative('compound_progress', [compound, ['intro', compound, 0, '_fresh', 'ind', p.refl(0)]])
    alpha_goal = ['D', 'a', 'b', Eq('b', 'b')]
    negative('introduction_eigen_escape', [alpha_goal,
                                          ['intro', alpha_goal, 0, 'b', 'case', p.refl(S('b'))]])
    major_eigen = p.fresh()
    major = ['intro', alpha_goal, 0, major_eigen, 'case', p.refl(S(major_eigen))]
    escaping = p.fresh()
    negative('elimination_eigen_escape', [Eq(0, 0),
                                         ['delim', major, escaping, p.refl(escaping)]])

    # Without the explicit witness/binder check, sequential opening would
    # capture the free witness y and prove this false standard arithmetic goal.
    capture_goal = ['D', 'x', 'y', Eq(I('y', 0, 'u', 'x'), I('y', 0, 'v', 'y'))]
    outer_goal = ['D', 'a', 'b', Eq(0, 0)]
    outer = ['intro', outer_goal, 0, '_outer', 'case', p.refl(0)]
    false_inner = ['intro', capture_goal, 'y', '_step', 'case',
                   p.refl(I(S('_step'), 0, 'u', S('_step')))]
    negative('closed_DI_capture_exploit', [capture_goal, ['delim', outer, 'y', false_inner]])

    # Alpha-equivalence and capture avoidance are semantic boundary tests.
    alpha_left = I(S(0), 0, 'u', I('u', 0, 'v', S('v')))
    alpha_right = I(S(0), 0, 'v', I('v', 0, 'u', S('u')))
    assert kernel.same(alpha_left, alpha_right)
    assert not kernel.same(I(S(0), 'x', 'u', 'x'), I(S(0), 'x', 'u', 'u'))
    captured = kernel.substitute(I(0, 0, 'y', S('x')), 'x', 'y')
    assert kernel.free(captured) == {'y'} and captured[3] != 'y'
    records.append({'label': 'alpha_and_capture_boundaries', 'expected': 'correct', 'passed': True})

    cli = []
    for optimize in (False, True):
        for item in packets:
            command = [sys.executable] + (['-O'] if optimize else []) + [str(ROOT / 'root_seed_checker.py')]
            result = subprocess.run(command, input=json.dumps(item['packet']), text=True,
                                    capture_output=True, timeout=10)
            expected_output = 'ACCEPT' if item['accept'] else 'REJECT'
            assert result.stdout.strip() == expected_output, (item['label'], result.stdout, result.stderr)
            assert (result.returncode == 0) == item['accept'], item['label']
            cli.append({'label': item['label'], 'optimized': optimize, 'passed': True})
    (ROOT / 'root_seed_fixtures.json').write_text(json.dumps(packets, indent=2) + '\n')
    (ROOT / 'root_seed_scoped_certificates.json').write_text(json.dumps(scoped_packets, indent=2) + '\n')
    receipt = {'api_checks': records, 'cli_checks': cli, 'all_passed': True,
               'scope': 'Finite executable checks of generated certificates and rejection controls; universal metatheory is a written proof.'}
    (ROOT / 'root_seed_validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'api_checks': len(records), 'cli_checks': len(cli), 'all_passed': True}, indent=2))


if __name__ == '__main__':
    main()
