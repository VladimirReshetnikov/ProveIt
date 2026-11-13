"""Focused reproducible certificates, exact-goal translations and substitutions.

These finite tests verify implementation paths; they do not replace the
written structural proof or claim a machine-checked iPRA bi-interpretation.
"""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys

import checker as fused
import control_split as split
import control_inherited as inherited
import measure
import translations as tr

ROOT = Path(__file__).resolve().parent
G = [([], [1, 1])]


def refl(t):
    return [t, t], ['u', 0, t, None]


def ev(P, Q):
    A, matched = tr.evaluate(P[0], Q[0], split.sub)
    if not matched:
        raise ValueError('arithmetic evaluation expected')
    return A, ['v', P[1], Q[1]]


def zero(a, h):
    return ev(refl(a), refl([0, a, h]))


def successor(c, a, h):
    return ev(refl([c, a, h]), refl([[0, c], a, h]))


def join(P, Q):
    s, _ = P[0]
    if Q[0][0] != s:
        raise ValueError('join needs a common left side')
    return ev(P, ev(Q, refl([0, s, 1])))


def symmetry(P):
    return join(refl(P[0][0]), P)


def transitivity(P, Q):
    if P[0][1] != Q[0][0]:
        raise ValueError('transitivity endpoint mismatch')
    return join(Q, symmetry(P))


def congruence(P, h):
    s, _ = P[0]
    z = zero(s, h)
    left = ev(z, refl([[0, 0], s, h]))
    right = ev(transitivity(z, P), refl([[0, 0], s, h]))
    return join(right, left)


def closed(P):
    result = {'goal': P[0], 'proof': P[1]}
    split.check(result)
    return tr.translate(result, split, fused, False, True)


def positive_cases():
    out = {}
    for i, t in enumerate([0, [0, 0], [0, [0, 0]], [0, 0, 1], [[0, 0], 0, [0, 1]]]):
        out['reflexivity_' + str(i)] = closed(refl(t))
    out['zero_computation'] = closed(zero([0, 0], [0, 1]))
    out['successor_computation'] = closed(successor([0, 0], 0, [0, 1]))
    out['symmetry'] = closed(symmetry(zero([0, 0], 1)))
    out['congruence_nested_iterator'] = closed(congruence(zero([0, 0], 1), [1, 0, [0, 1]]))

    out['compound_identity'] = {'goal': [0, 0],
        'proof': ['e', tr.theta(1), tr.theta(2), refl(0)[1]]}
    out['use_opened_clause'] = {'goal': [0, 0],
        'proof': ['e', tr.theta(1), tr.theta(2), ['u', 1, [0, 0], refl(0)[1]]]}
    out['nested_compound_introduction'] = {'goal': [[[0, 0]]],
        'proof': ['i', [[0, 0]], [0, 0], tr.theta(2)]}

    # The branch really cites its introduced hypothesis through congruence.
    # In the first case a nonzero witness still selects progress. In the
    # second an atomic matrix at witness zero selects cases. Both contrast
    # with the inherited witness-dependent introduction on these certificates.
    for name, B0, t in [
        ('diagonal_progress_nonzero_witness', [[1, 1, 1], [1, 1, 1]], [0, 0]),
        ('nondiagonal_cases_zero_witness', [[1, 0, 1], [1, 0, 1]], 0),
    ]:
        B = split.sub(B0, t, 1)
        H = split.sub(B, -1 if tr.diagonal(B0) else 0)
        target = split.sub(B, [0, -1])
        step = congruence((H, ['u', 1, 0, None]), target[0])
        if step[0] != target:
            raise ValueError('generated introduction target differs')
        out[name] = closed(([B0], ['i', B0, t, step[1]]))

    local = G + [([0, 0], [0, 0])]
    # Both computations can erase a witness that occurs in their premises.
    E0, E0p = zero(-1, 0)
    F0, F0p = ev((E0, E0p), refl([[0, 0], -1, 0]))
    _, e0 = tr.between(E0p, split, fused, False, True, sc=local, tg=local)
    _, f0 = tr.between(F0p, split, fused, False, True, sc=local, tg=local)
    out['successor_evaluation_erases_witness'] = {
        'goal': [0, 0], 'proof': ['e', tr.theta(1), e0, f0]}
    _, zproof = tr.between(zero(0, -1)[1], split, fused, False, True,
                          sc=local, tg=local)
    out['zero_evaluation_erases_witness'] = {
        'goal': [0, 0], 'proof': ['e', tr.theta(1), refl(0)[1], zproof]}
    return out


def negative_cases(positives):
    truth = deepcopy(positives['reflexivity_0'])
    out = {
        'false_equation': {'goal': [0, [0, 0]], 'proof': refl(0)[1]},
        'unmatched_equation_has_no_identity_case': {
            'goal': [0, 0], 'proof': ['e', tr.theta(1), refl(0)[1], refl(0)[1]]},
        'witness_escape_through_identity': {
            'goal': [0, 0], 'proof': ['e', tr.theta(1), tr.theta(2), refl(-1)[1]]},
        'wrong_major_sort': {'goal': [0, 0], 'proof': ['e', refl(0)[1], tr.theta(2), refl(0)[1]]},
        'missing_goal': {'proof': refl(0)[1]},
        'extra_key': truth | {'extra': 0},
        'empty_proof': truth | {'proof': []},
        'unknown_rule': truth | {'proof': ['v', refl(0)[1], refl(0)[1]]},
        'boolean_clause_index': truth | {'proof': ['u', False, 0, None]},
        'negative_clause_index': truth | {'proof': ['u', -1, 0, None]},
        'out_of_scope_clause_index': truth | {'proof': ['u', 1, 0, None]},
        'unused_proof_field_not_null': truth | {'proof': ['u', 0, 0, {'unvalidated': True}]},
        'invalid_intro_witness': {'goal': [[0, 0]], 'proof': ['i', [0, 0], -1, ['u', 1, 0, None]]},
    }
    malformed_terms = {
        'boolean': False, 'float': 0.0, 'string': '0', 'dict': {},
        'free_level': -1, 'unbound_index': 1, 'empty': [],
        'unary': [0], 'arity_four': [0, 0, 0, 0],
        'successor_tag': [1, 0], 'bad_iter_body': [0, 0, True],
        'loose_iter_index': [0, 0, 2],
    }
    for name, t in malformed_terms.items():
        out['term_' + name] = {'goal': [t, t], 'proof': refl(t)[1]}
    wrong = deepcopy(positives['diagonal_progress_nonzero_witness'])
    # Change only one seed to break the diagonal while keeping the old proof.
    wrong['goal'][0][0][1] = 0
    wrong['proof'][1][0][1] = 0
    out['changed_diagonal_mode'] = wrong
    return out


def rejects(module, data):
    try:
        module.check(data)
    except Exception:
        return True
    return False


def substitution_checks():
    context = G + [([], [0, 0])]
    tests = []
    for P in [zero(-1, [0, 1]), successor(-1, 0, [0, 1]),
              congruence(zero(-1, 1), [1, -1, [0, 1]])]:
        _, fp = tr.between(P[1], split, fused, False, True,
                           sc=context, tg=context)
        A = fused.prove(fp, context)
        for t in [0, [0, 0], [[0, 0], 0, [0, 1]]]:
            sigma = {-1: t}
            renamed = tr.substitute_proof(fp, sigma)
            expected = tr.rename(A, sigma)
            if fused.prove(renamed, context) != expected:
                raise ValueError('free substitution changed the inferred conclusion')
            tests.append({'source_goal': A, 'parameter_image': t,
                          'substituted_goal': expected})

    # A formerly unmatched equation can become a positive row. This is why
    # total rho with an arbitrary fallback is not covariant, while partial
    # rho only asserts covariance on its defined inputs.
    E, F = [-1, 0], [[0, 0, 0], 0]
    try:
        tr.evaluate(E, F, fused.sub)
    except ValueError:
        pass
    else:
        raise ValueError('partial rho unexpectedly accepted the old fallback')
    result, matched = tr.evaluate(tr.rename(E, {-1: 0}), F, fused.sub)
    if not matched or result != [0, 0] or result == F:
        raise ValueError('fallback substitution witness is wrong')

    matrices = [
        [[1, 1, -1], [1, 1, 1]],
        [[1, 0, -1], [1, 1, 1]],
        [[-1, 1, 1], [1, 1, 1]],
        [[1, -1, 1], [1, 1, 1]],
        [[[1, 1, 1], [1, 1, 1]]],
    ]
    for B in matrices:
        for t in [0, [0, 0], [0, 0, 1], -2]:
            if tr.diagonal(B) != tr.diagonal(tr.rename(B, {-1: t})):
                raise ValueError('diagonal selector changed under free substitution')
    return {'proof_substitutions': tests, 'diagonal_substitution_pairs': 20,
            'old_total_rho_counterexample': {'E': E, 'F': F, 'substitution': {'-1': 0},
                                           'new_defined_value': result}}


def main():
    metrics = measure.main()
    positives = positive_cases()
    negatives = negative_cases(positives)
    counts = {'accepted': 0, 'rejected': 0, 'exact_goal_roundtrips': 0,
              'cli_runs': 0, 'readable_cli_runs': 0, 'normalized_cli_runs': 0}
    for name, data in positives.items():
        fused.check(data)
        control_data = tr.translate(data, fused, split, True, False)
        again = tr.translate(control_data, split, fused, False, True)
        if again['goal'] != data['goal']:
            raise ValueError('round trip altered its goal')
        counts['accepted'] += 1
        counts['exact_goal_roundtrips'] += 1
        (ROOT / 'tests' / 'accept' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    for name, data in negatives.items():
        if not rejects(fused, data):
            raise ValueError('invalid certificate accepted: ' + name)
        counts['rejected'] += 1
        (ROOT / 'tests' / 'reject' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    for module, coordinate in [('checker.py', 'readable_cli_runs'),
                               ('checker_normalized.py', 'normalized_cli_runs')]:
        for flag in [[], ['-O']]:
            for expected, cases in [(True, positives), (False, negatives)]:
                for name, data in cases.items():
                    run = subprocess.run([sys.executable, *flag, str(ROOT / module)],
                                         input=json.dumps(data), text=True, capture_output=True,
                                         timeout=20)
                    accepted = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
                    if accepted != expected:
                        raise ValueError('CLI result differs: ' + module + ':' + name)
                    counts['cli_runs'] += 1
                    counts[coordinate] += 1
    differences = {
        name: {'new_accepts': not rejects(fused, positives[name]),
               'inherited_accepts_same_certificate': not rejects(inherited, positives[name])}
        for name in ['diagonal_progress_nonzero_witness', 'nondiagonal_cases_zero_witness']}
    fallback = negatives['unmatched_equation_has_no_identity_case']
    differences['unmatched_identity_removed'] = {
        'new_accepts': not rejects(fused, fallback),
        'inherited_accepts_same_certificate': not rejects(inherited, fallback)}
    result = {'status': 'all passed', 'python': sys.version.split()[0], 'counts': counts,
              'rule_differences': differences, 'substitution': substitution_checks(),
              'metrics': metrics,
              'limits': 'Finite implementation evidence; written universal proofs; no new Lean theorem.'}
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'counts': counts,
                      'rule_differences': differences, 'metrics': result['metrics']}, indent=2))


if __name__ == '__main__':
    main()
