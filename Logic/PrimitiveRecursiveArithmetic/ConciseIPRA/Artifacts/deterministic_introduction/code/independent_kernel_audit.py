"""Targeted independent checks of deterministic introduction and binder handling.

No proof builders or translators from verify.py are imported.  The fixtures
below use hand-stated conclusions.  This is finite regression evidence, not
a formal verification of the checker or the mathematical equivalence.
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
DEFAULT = HERE if (HERE / 'checker.py').exists() else HERE / 'parameter_intro_code'
DIRECTORY = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT
SPEC = importlib.util.spec_from_file_location('independently_audited_kernel', DIRECTORY / 'checker.py')
K = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(K)


def require(condition, description):
    if not condition:
        raise AssertionError(description)


def S(t):
    return [0, t]


def I(n, a, h):
    return [n, a, h]


def D(matrix):
    return [matrix]


def N(t):
    # Under D(x,y) and the iterator state: state=1, y=2, x=3.
    return [I(1, 0, 3), I(1, 0, t)]


def reflexivity(t):
    p = ['zero', t, 0]
    return ['tr', [1, t], p, p]


def naming(t, parent_scope=0):
    z = -parent_scope - 1
    return ['intro', N(t), reflexivity(I(S(z), 0, t))]


def rejected_by_infer(proof):
    try:
        K.infer(proof)
    except Exception:
        return True
    return False


def main():
    # The target has genuinely bound indices of its own.  These must remain
    # bound when the target is inserted below several external binders.
    h = I(1, 1, 2)
    source = I(0, 0, h)
    equation = ['zero', 0, h]  # source = 0
    one = ['tr', D(N(4)), equation, naming(source)]
    two_minor = ['intro', D(N(source)), naming(source, 1)]
    two = ['tr', D(D(N(6))), equation, two_minor]

    # A second nested-body example checks replacement and index removal in
    # the successor computation independently of the transport fixtures.
    body = I(0, 1, 2)
    previous = I(0, 0, body)
    successor_goal = [I(S(0), 0, body), I(0, previous, previous)]
    positives = {
        'transport_under_one_guarded_D': {'goal': D(N(0)), 'proof': one},
        'transport_under_two_guarded_Ds': {'goal': D(D(N(0))), 'proof': two},
        'successor_substitution_under_inner_iterator': {
            'goal': successor_goal, 'proof': ['succ', 0, 0, body]},
    }

    wrong_one = copy.deepcopy(one)
    wrong_one[1] = D(N(3))  # This is the bound witness, not the transport hole.
    wrong_two = copy.deepcopy(two)
    wrong_two[1] = D(D(N(5)))  # Outer D binder, not the transport hole at 6.
    escaped = ['open', naming(0), ['zero', 0, I(0, 0, -1)]]
    negatives = {
        'transport_cannot_replace_bound_witness': {
            'goal': D(N(0)), 'proof': wrong_one},
        'transport_cannot_replace_outer_D_variable': {
            'goal': D(D(N(0))), 'proof': wrong_two},
        'opened_witness_hidden_in_dead_iterator_body': {
            'goal': [[0, 0, 0], 0], 'proof': escaped},
    }

    direct_checks = []
    require(K.witness(N(source), 0) == source,
            'A target with only internally bound indices must be recognized')
    direct_checks.append('name_target_with_internal_binders_is_recognized')
    hidden_witness = I(0, 0, 4)
    require(K.formula(D(N(hidden_witness)), 0),
            'The negative naming fixture must be a valid guarded formula')
    require(K.witness(N(hidden_witness), 0) == 0,
            'A nested reference to the matrix witness is not outer scoped')
    direct_checks.append('nested_matrix_witness_is_not_a_naming_target')
    require(K.sub(D(D(N(6))), source) == D(D(N(source))),
            'Transport-hole substitution must cross exactly five binders')
    direct_checks.append('full_formula_substitution_crosses_five_binders')
    require(K.sub(body, previous) == I(0, previous, previous),
            'Successor computation must remove the outer state binder')
    direct_checks.append('successor_body_substitution_removes_outer_binder')
    require(rejected_by_infer(escaped),
            'Open must reject escape during inference, before goal comparison')
    direct_checks.append('hidden_eigenparameter_rejected_inside_infer')

    runs = []
    for expected, fixtures in [(True, positives), (False, negatives)]:
        for name, data in fixtures.items():
            if expected:
                K.check(data)
            else:
                try:
                    K.check(data)
                except Exception:
                    pass
                else:
                    raise AssertionError(name + ' was unexpectedly accepted')
            for optimized in [False, True]:
                command = [sys.executable] + (['-O'] if optimized else []) + [str(DIRECTORY / 'checker.py')]
                result = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True)
                accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
                require(accepted == expected, (name, optimized, result.returncode, result.stdout, result.stderr))
                runs.append({'case': name, 'optimized': optimized,
                             'expected_accept': expected, 'accepted': accepted})

    report = {
        'assessment': 'No mismatch found in the independently inspected kernel operations.',
        'positive_fixtures': len(positives),
        'negative_fixtures': len(negatives),
        'direct_checks': direct_checks,
        'cli_runs': len(runs),
        'runs': runs,
        'formal_verification': False,
    }
    output = DIRECTORY / 'independent_kernel_audit.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
