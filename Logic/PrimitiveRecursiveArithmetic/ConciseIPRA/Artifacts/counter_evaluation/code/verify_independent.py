"""Independent constructions and semantic checks for counter evaluation.

No imports from the verifier except its public checking API are used for
the expected equations, bound-variable substitution, or arithmetic semantics.
Run: python3 verify_independent.py [path/to/counter_eval.py]
"""
from __future__ import annotations
import copy
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys


HERE = Path(__file__).resolve().parent
DEFAULT_CHECKER = HERE / 'counter_eval.py'
if not DEFAULT_CHECKER.exists():
    DEFAULT_CHECKER = HERE.parent / 'counter_candidate/counter_eval.py'
CHECKER = Path(sys.argv[1]) if __name__ == '__main__' and len(sys.argv) > 1 else DEFAULT_CHECKER
spec = importlib.util.spec_from_file_location('checked_module', CHECKER)
kernel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernel)


from proof_macros import *


def run():
    positives = []
    open_results = []
    template_results = []
    semantic_results = 0
    rng = random.Random(7331)
    templates = [1, S(1), P(1), C(1, 0, S(1)),
                 R(S(1), 1, R(S(3), 1, S(2)))]
    templates += [random_term(rng, 1, 4) for _ in range(24)]
    for k, h in enumerate(templates):
        assert kernel.term(h, 0, 1)
        s, t, r = -1, -2, -3
        eq = [s, t]
        eq_h = [instantiate(h, [s]), r]
        p = hypothesis(eq, 0)
        q = hypothesis(eq_h, 1)
        context = [([0, 0], eq), ([0, 0], eq_h)]
        cp = congruence(h, p)
        tp = transport(h, p, q)
        assert cp[0] == [instantiate(h, [s]), instantiate(h, [t])]
        assert tp[0] == [r, instantiate(h, [t])]
        assert kernel.derive(cp[1], context, 3) == cp[0]
        assert kernel.derive(tp[1], context, 3) == tp[0]
        assert nodes(cp[1]) == nodes(p[1]) + 4
        assert nodes(tp[1]) == nodes(p[1]) + nodes(q[1]) + 7
        template_results.append({'template': k, 'congruence_nodes_added': 4,
                                 'transport_nodes_added': 7})
        closed_p = computation(0, 0, 2)
        closed = congruence(h, closed_p)
        positives.append((f'nested_congruence_{k:02}', {'goal': closed[0], 'proof': closed[1]}))

    for k in range(30):
        h = random_term(rng, 2, 4, free=2)
        n, seed = -1, -2
        p = computation(n, seed, h)
        assert p[0] == [R(S(n), seed, h), instantiate(h, [R(n, seed, h), n])]
        assert kernel.derive(p[1], [], 2) == p[0]
        open_results.append({'case': k, 'kind': 'nested simultaneous substitution'})
        for nval in range(4):
            free = {-1: nval, -2: 1}
            try:
                left = term_value(p[0][0], free)
                right = term_value(p[0][1], free)
            except OverflowError:
                continue
            assert left == right
            semantic_results += 1

    s, t, r = -1, -2, -3
    p, q = hypothesis([s, t], 0), hypothesis([s, r], 1)
    rp = root(p, q)
    assert rp[0] == [r, t]
    assert kernel.derive(rp[1], [([0, 0], p[0]), ([0, 0], q[0])], 3) == [r, t]
    assert nodes(rp[1]) == nodes(p[1]) + nodes(q[1]) + 3

    n, a, b = -1, -2, -3
    for name, p, expected in [
        ('selector_zero', c_zero(a, b), [C(0, a, b), a]),
        ('selector_successor', c_step(n, a, b), [C(S(n), a, b), b]),
    ]:
        assert p[0] == expected
        assert kernel.derive(p[1], [], 3) == expected
        open_results.append({'case': name, 'kind': 'arithmetic compiler equation'})
    step_bodies = [1, 2, S(1), S(2), C(2, 1, S(1)), R(S(2), 1, S(1))]
    for k, body in enumerate(step_bodies):
        for p, expected in [
            (rec_zero(a, body), [Rec(0, a, body), a]),
            (rec_step(n, a, body), [Rec(S(n), a, body), instantiate(body, [Rec(n, a, body), n])]),
        ]:
            assert p[0] == expected
            assert kernel.derive(p[1], [], 2) == expected
            open_results.append({'case': k, 'kind': 'primitive recursion defining equation'})

    for nval in range(9):
        numerator = 0
        for _ in range(nval):
            numerator = S(numerator)
        assert term_value(P(S(numerator))) == nval
        semantic_results += 1
        for aval in range(5):
            for bval in range(5):
                v = term_value(C(-1, -2, -3), {-1: nval, -2: aval, -3: bval})
                assert v == (aval if nval == 0 else bval)
                semantic_results += 1
        for aval in range(4):
            for body in step_bodies:
                state = aval
                try:
                    for index in range(nval):
                        state = term_value(body, bound=(state, index))
                    observed = term_value(Rec(-1, -2, body), {-1: nval, -2: aval})
                except OverflowError:
                    continue
                assert state == observed
                semantic_results += 1

    positives.append(('reflexivity', {'goal': [0, 0], 'proof': ['r', 0]}))
    positives.append(('successor_computation', {'goal': computation(S(0), 0, S(1))[0],
                                               'proof': computation(S(0), 0, S(1))[1]}))
    compound_goal = [[[3, 3]]]
    inner_goal = [[S(-1), S(-1)]]
    positives.append(('compound_case_introduction', {
        'goal': compound_goal,
        'proof': ['i', compound_goal, 0, ['i', inner_goal, 0, ['r', S(-1)]]]}))
    case_goal = [[C(1, 2, 2), 2]]
    for label, witness in [('successor', S(0)), ('computable_zero', P(S(0)))]:
        positives.append(('witness_case_' + label, {
            'goal': case_goal,
            'proof': ['i', case_goal, witness, c_step(-1, witness, witness)[1]]}))
    for name, target in [('zero', 0), ('three', S(S(S(0)))), ('nested', P(S(S(0))))]:
        positives.append((f'used_induction_{name}', induction_certificate(target)))

    negatives = [
        ('false_equality', {'goal': [0, S(0)], 'proof': ['r', 0]}),
        ('invalid_counter_source', {'goal': [0, 0], 'proof': ['v', ['r', 0], ['r', R(S(S(0)), 0, 2)]]}),
        ('boolean_term', {'goal': [False, False], 'proof': ['r', False]}),
        ('boolean_index', {'goal': [[1, 1]], 'proof': ['i', [[1, 1]], 0, ['u', False, 0, ['r', 0]]]}),
        ('unbound_positive', {'goal': [1, 1], 'proof': ['r', 1]}),
        ('unbound_negative', {'goal': [-1, -1], 'proof': ['r', -1]}),
        ('noncanonical_zero_body', {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': ['r', [0, 0, 1]]}),
        ('counter_state_slots_swapped', {
            'goal': [R(S(0), 0, 1), 0],
            'proof': computation(0, 0, 1)[1]}),
        ('extra_top_field', {'goal': [0, 0], 'proof': ['r', 0], 'extra': 1}),
        ('unknown_rule', {'goal': [0, 0], 'proof': ['unknown', 0]}),
        ('extra_rule_field', {'goal': [0, 0], 'proof': ['r', 0, 0]}),
        ('witness_escape', {'goal': [[1, 1]], 'proof': ['i', [[1, 1]], -1, ['r', S(-1)]]}),
        ('unused_false_progress', {'goal': [[0, S(0)]], 'proof': ['i', [[0, S(0)]], 0, ['r', 0]]}),
    ]
    attack = copy.deepcopy(induction_certificate(S(0)))
    def destroy_hypothesis(tree):
        if tree[0] == 'u':
            return ['r', 0]
        if tree[0] == 'v':
            return ['v', destroy_hypothesis(tree[1]), destroy_hypothesis(tree[2])]
        return tree
    attack['proof'][2][3] = destroy_hypothesis(attack['proof'][2][3])
    negatives.append(('induction_hypothesis_removed', attack))
    attack2 = copy.deepcopy(induction_certificate(S(0)))
    attack2['proof'][1] = [-1, -1]
    negatives.append(('elimination_eigenvariable_escape', attack2))

    out = HERE / 'certificates'
    out.mkdir(exist_ok=True)
    process_results = []
    for accepted, cases in [(True, positives), (False, negatives)]:
        for name, certificate in cases:
            if accepted:
                assert kernel.verify(certificate)
            else:
                try:
                    kernel.verify(certificate)
                except Exception:
                    pass
                else:
                    raise AssertionError(('accepted invalid certificate', name))
            (out / (name + '.json')).write_text(json.dumps(certificate, indent=2) + '\n')
            for optimized in [False, True]:
                command = [sys.executable] + (['-O'] if optimized else []) + [str(CHECKER)]
                result = subprocess.run(command, input=json.dumps(certificate), text=True, capture_output=True)
                observed = result.returncode == 0 and result.stdout == 'ACCEPT\n'
                assert observed == accepted, (name, optimized, result.stdout, result.stderr)
                if not accepted:
                    assert result.returncode != 0 and result.stdout == 'REJECT\n'
                process_results.append({'name': name, 'optimized': optimized, 'expected_accept': accepted,
                                        'exit_code': result.returncode, 'output': result.stdout.strip()})
    report = {'positive_certificates': len(positives), 'negative_certificates': len(negatives),
              'public_process_checks': len(process_results), 'open_equational_checks': len(open_results),
              'template_checks': template_results, 'finite_semantic_checks': semantic_results,
              'root_composition_nodes_added': 3, 'congruence_nodes_added': 4,
              'crossed_transport_nodes_added': 7, 'mismatches': 0,
              'checks': process_results, 'open_checks': open_results}
    evidence = HERE.parent / 'evidence' if (HERE / 'counter_eval.py').exists() else HERE
    evidence.mkdir(exist_ok=True)
    (evidence / 'independent_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ['checks', 'open_checks', 'template_checks']}, indent=2))


if __name__ == '__main__':
    run()
