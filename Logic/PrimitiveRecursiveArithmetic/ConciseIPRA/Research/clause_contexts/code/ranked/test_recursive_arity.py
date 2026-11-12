"""Matched-control verification for the recursive arity codec."""
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

import checker_recursive_arity as checker
import translate_recursive as translate

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'horn'


def check(certificate, optimized):
    command = [sys.executable] + (['-O'] if optimized else [])
    command.append(str(ROOT / 'checker_recursive_arity.py'))
    result = subprocess.run(command, input=json.dumps(certificate), text=True,
                            capture_output=True, timeout=10)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def negative_cases():
    truth, reflexivity = [0, 0], ['u', 0, 0, []]
    cases = {}
    for name, formula in [('integer', 0), ('empty', []), ('singleton', [0]),
                         ('triple', [0, 0, 0]), ('unknown_tag', ['q', [0, 0]]),
                         ('bad_d_body', ['d', 0]), ('empty_d_body', ['d', []]),
                         ('scope_under_d', ['d', [3, 3]])]:
        cases['formula_' + name] = {'goal': formula, 'proof': reflexivity}
    for name, term in [('free_index', 1), ('future_level', -1),
                      ('boolean', False), ('float', 0.0), ('string', 'd'),
                      ('empty_term', []), ('binary_term', [0, 0]),
                      ('zero_iterator', [0, 0, 0]),
                      ('escaping_body', [[0], 0, 2])]:
        cases['term_' + name] = {'goal': [term, term],
                                'proof': ['u', 0, term, []]}
    for name, index in [('negative', -1), ('boolean', False),
                        ('float', 0.0), ('absent', 1)]:
        cases['index_' + name] = {'goal': truth, 'proof': ['u', index, 0, []]}
    for name, premises in [('null', None), ('false', False), ('mapping', {}),
                           ('extra', [reflexivity])]:
        cases['premises_' + name] = {'goal': truth,
                                   'proof': ['u', 0, 0, premises]}
    cases['false_equation'] = {'goal': [0, [0]], 'proof': reflexivity}
    cases['extra_field'] = {'goal': truth, 'proof': reflexivity, 'extra': 0}
    compound = ['i', ['d', [1, 1]], 0, ['u', 0, [-1], []]]
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
    cases['di_eigenvariable_escape'] = {'goal': ['d', [1, 1]],
        'proof': ['i', ['d', [1, 1]], 0, ['u', 0, [-2], []]]}
    cases['di_witness_escape'] = {'goal': ['d', [1, 1]],
        'proof': ['i', ['d', [1, 1]], -1, ['u', 0, [-1], []]]}
    cases['removed_refl_rule'] = {'goal': truth, 'proof': ['r', 0]}
    return cases


def main():
    spec = importlib.util.spec_from_file_location('tagged', SOURCE / 'checker.py')
    tagged = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tagged)
    files = sorted((SOURCE / 'examples').glob('*.json'))
    destination = ROOT / 'recursive_examples'
    destination.mkdir(exist_ok=True)
    for path in files:
        original = json.loads(path.read_text())
        certificate = translate.forward(original)
        assert translate.backward(certificate) == original
        assert tagged.verify(original) and checker.verify(certificate)
        for optimized in (False, True):
            assert check(certificate, optimized), (path, optimized)
        (destination / path.name).write_text(json.dumps(certificate, separators=(',', ':')) + '\n')
    negatives = negative_cases()
    for name, certificate in negatives.items():
        for optimized in (False, True):
            assert not check(certificate, optimized), (name, optimized)
    rng = random.Random(20261111)
    def term(scope, depth, budget):
        if budget <= 0 or rng.randrange(4) == 0:
            return rng.randint(-scope, depth)
        if rng.randrange(3) == 0:
            return [term(scope, depth, budget - 1)]
        return checker.iterator(term(scope, depth, budget - 1),
                                term(scope, depth, budget - 1),
                                term(scope, depth + 1, budget - 1))
    for unused in range(2000):
        scope, k, external = rng.randrange(4), rng.randrange(7), rng.randrange(2)
        formula = [term(scope, 2 * k + external + 1, 3),
                   term(scope, 2 * k + external + 1, 3)]
        for ignored in range(k):
            formula = ['d', formula]
        witness = term(scope, 0, 3)
        old = tagged.opening(translate.formula_backward(formula),
                             translate.term_backward(witness), external)
        new = checker.opening(formula, witness, external)
        assert translate.formula_forward(old) == new
        assert checker.formula(new, scope, external)
    result = {'positive_certificates': len(files),
              'negative_certificates': len(negatives),
              'substitution_coherence_instances': 2000,
              'optimized_python_checked': True,
              'standalone_processes': 2 * (len(files) + len(negatives)),
              'negative_names': list(negatives)}
    (ROOT / 'verification_recursive.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'negative_names'}, indent=2))


if __name__ == '__main__':
    main()
