"""Independent syntax, scope, substitution, and certificate checks."""
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

import translate
import checker_ranked_arity as ranked

ROOT = Path(__file__).resolve().parent
REFERENCE = ROOT.parent / 'horn' / 'checker.py'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(path, certificate, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=json.dumps(certificate), text=True,
                            capture_output=True, timeout=10)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def rejected_certificates():
    truth = [0, 0, 0]
    reflexivity = ['u', 0, 0, []]
    cases = {}
    for name, k in [('negative', -1), ('false', False), ('true', True),
                    ('float', 0.0), ('null', None), ('list', []), ('string', '0')]:
        cases['rank_' + name] = {'goal': [k, 0, 0], 'proof': reflexivity}
    for name, a in [('free_index', 1), ('future_level', -1),
                    ('boolean', False), ('float', 0.0), ('string', '0'),
                    ('empty_term', []), ('binary_term', [0, 0]),
                    ('zero_iterator', [0, 0, 0]),
                    ('escaping_body', [[0], 0, 2])]:
        cases['term_' + name] = {'goal': [0, a, a], 'proof': ['u', 0, a, []]}
    cases['rank_one_scope_escape'] = {'goal': [1, 3, 3],
        'proof': ['i', [1, 3, 3], 0, reflexivity]}
    for name, index in [('negative', -1), ('boolean', False), ('float', 0.0),
                        ('absent', 1)]:
        cases['clause_index_' + name] = {'goal': truth,
            'proof': ['u', index, 0, []]}
    for name, premises in [('null', None), ('false', False), ('mapping', {}),
                           ('extra', [reflexivity])]:
        cases['reflexivity_premises_' + name] = {'goal': truth,
            'proof': ['u', 0, 0, premises]}
    cases['false_equation'] = {'goal': [0, 0, [0]], 'proof': reflexivity}
    cases['extra_field'] = {'goal': truth, 'proof': reflexivity, 'extra': 0}
    cases['extra_goal_entry'] = {'goal': [0, 0, 0, 0], 'proof': reflexivity}
    cases['nonformula_goal'] = {'goal': 0, 'proof': reflexivity}
    cases['wrong_step_source'] = {'goal': truth,
        'proof': ['x', reflexivity, ['u', 0, [[0], [0], 1], []]]}
    compound = ['i', [1, 1, 1], 0, ['u', 0, [-1], []]]
    cases['compound_step_major'] = {'goal': truth,
        'proof': ['x', compound, ['u', 0, [[0], 0, 1], []]]}
    cases['compound_step_minor'] = {'goal': truth,
        'proof': ['x', reflexivity, compound]}
    cases['missing_clause_base'] = {'goal': truth,
        'proof': ['e', truth, compound, ['u', 1, 0, []]]}
    cases['wrong_clause_base'] = {'goal': truth,
        'proof': ['e', truth, compound, ['u', 1, 0, [['u', 0, [0], []]]]]}
    cases['de_eigenvariable_escape'] = {'goal': truth,
        'proof': ['e', truth, compound, ['u', 0, -2, []]]}
    cases['di_eigenvariable_escape'] = {'goal': [1, 1, 1],
        'proof': ['i', [1, 1, 1], 0, ['u', 0, [-2], []]]}
    cases['di_witness_escape'] = {'goal': [1, 1, 1],
        'proof': ['i', [1, 1, 1], -1, ['u', 0, [-1], []]]}
    cases['removed_refl_rule'] = {'goal': truth, 'proof': ['r', 0]}
    return cases


def syntax_checks(reference, count=2000):
    rng = random.Random(20261111)

    def term(scope, depth, budget):
        if budget <= 0 or rng.randrange(4) == 0:
            return rng.randint(-scope, depth)
        if rng.randrange(3) == 0:
            return [term(scope, depth, budget - 1)]
        return ranked.iterator(term(scope, depth, budget - 1),
                               term(scope, depth, budget - 1),
                               term(scope, depth + 1, budget - 1))

    for unused in range(count):
        scope = rng.randrange(4)
        k = rng.randrange(7)
        external = rng.randrange(2)
        f = [k, term(scope, 2 * k + external + 1, 3),
                term(scope, 2 * k + external + 1, 3)]
        witness = term(scope, 0, 3)
        native = translate.formula_backward(f)
        assert translate.formula_forward(native) == f
        native_witness = translate.term_backward(witness)
        old = reference.opening(native, native_witness, external)
        new = ranked.instance(f, witness, external)
        assert translate.formula_forward(old) == new
        assert reference.formula(old, scope, external)
        assert ranked.term(witness, scope)
    return count


def main():
    reference = load('tagged_control', REFERENCE)
    checkers = [ROOT / 'checker_ranked_arity.py', ROOT / 'checker_ranked_scoped.py']
    examples = sorted((ROOT / 'examples').glob('*.json'))
    positives = []
    for path in examples:
        certificate = json.loads(path.read_text())
        native = translate.backward(certificate)
        assert translate.forward(native) == certificate, path
        assert reference.verify(native), path
        for checker in checkers:
            for optimized in (False, True):
                assert check(checker, certificate, optimized), (checker, path, optimized)
        positives.append(path.name)
    negatives = rejected_certificates()
    for name, certificate in negatives.items():
        for checker in checkers:
            for optimized in (False, True):
                assert not check(checker, certificate, optimized), (checker, name, optimized)
    substitutions = syntax_checks(reference)
    result = {'positive_certificates': len(positives),
              'rank_specific_negative_certificates': len(negatives),
              'checked_substitution_instances': substitutions,
              'checker_processes_per_certificate': 4,
              'optimized_python_checked': True,
              'bidirectional_certificate_round_trips': len(positives),
              'positive_names': positives, 'negative_names': list(negatives),
              'limitation': 'Finite tests are not a proof of soundness or bi-interpretability.'}
    (ROOT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('positive_names', 'negative_names')}, indent=2))


if __name__ == '__main__':
    main()
