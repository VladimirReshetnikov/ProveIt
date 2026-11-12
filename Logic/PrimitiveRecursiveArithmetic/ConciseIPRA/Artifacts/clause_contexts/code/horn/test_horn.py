"""Finite regression, translation, rejection, and substitution checks.

These tests are not a proof of consistency or of the interpretation theorem.
Every certificate check uses a standalone process, both normally and with -O.
"""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

import translate


ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('source_suite', ROOT / 'reference' / 'source_suite.py')
suite = importlib.util.module_from_spec(spec)
spec.loader.exec_module(suite)
horn = translate.horn


def check(path, certificate, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=json.dumps(certificate), text=True,
                            capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def adapted_negative(proof, kinds=()):
    """Change only the certificate representation, retaining invalid operands."""
    match proof:
        case ['r', term]:
            return ['u', 0, term, []]
        case ['x', major, minor]:
            return ['x', adapted_negative(major, kinds), adapted_negative(minor, kinds)]
        case ['u', index, witness, premise]:
            valid = type(index) is int and 0 <= index < len(kinds)
            premises = [] if valid and kinds[index] else [adapted_negative(premise, kinds)]
            shifted = index + 1 if type(index) is int and index >= 0 else index
            return ['u', shifted, witness, premises]
        case ['e', goal, major, branch]:
            return ['e', goal, adapted_negative(major, kinds), adapted_negative(branch, kinds + (False,))]
        case ['i', goal, witness, branch]:
            return ['i', goal, witness, adapted_negative(branch, kinds + (True,))]
    return copy.deepcopy(proof)


def hard_negatives():
    truth = ['=', 0, 0]
    one = ['s', 0]
    R = lambda t: ['u', 0, t, []]
    dgoal = ['d', ['=', 1, 1]]
    dproof = ['i', dgoal, 0, R(['s', -1])]
    cases = {}
    for name, index in [('negative', -1), ('boolean_false', False), ('boolean_true', True),
                        ('float', 0.0), ('absent', 1), ('mapping', {})]:
        cases['initial_clause_index_' + name] = {'goal': truth, 'proof': ['u', index, 0, []]}
    for name, premises in [('null', None), ('mapping', {}), ('string', ''), ('boolean', False),
                           ('unnecessary_proof', [R(0)]), ('malformed_proof', [[]])]:
        cases['initial_clause_premises_' + name] = {'goal': truth, 'proof': ['u', 0, 0, premises]}
    for name, premises in [('missing', []), ('duplicated', [R(0), R(0)]),
                           ('wrong_base', [R(one)]), ('bad_proof', [['magic']])]:
        cases['conditional_clause_' + name] = {
            'goal': ['=', one, one],
            'proof': ['e', ['=', one, one], dproof, ['u', 1, one, premises]],
        }
    nested = ['d', ['d', truth]]
    cases['local_fact_has_extra_premise'] = {
        'goal': nested,
        'proof': ['i', nested, 0, ['u', 1, 0, [R(0)]]],
    }
    for name, witness in [('positive', 1), ('future', -2), ('boolean', True),
                          ('bad_iterator_binder', ['i', one, 0, 2])]:
        cases['use_witness_' + name] = {'goal': ['d', truth],
            'proof': ['i', ['d', truth], 0, ['u', 1, witness, []]]}
    cases['unknown_removed_reflexivity_tag'] = {'goal': truth, 'proof': ['r', 0]}
    cases['duplicate_top_key_surrogate'] = {'goal': truth, 'proof': R(0), 'proof2': R(0)}
    cases['extra_use_argument'] = {'goal': truth, 'proof': ['u', 0, 0, [], []]}
    cases['step_compound_major'] = {'goal': truth, 'proof': ['x', dproof, R(['i', one, 0, 1])]}
    cases['step_compound_minor'] = {'goal': truth, 'proof': ['x', R(0), dproof]}
    cases['step_wrong_body'] = {'goal': truth,
        'proof': ['x', R(['i', one, 0, 1]), R(['i', ['s', one], 0, ['s', 1]])]}
    cases['de_internal_eigenvariable_escape'] = {'goal': truth,
        'proof': ['e', truth, dproof, ['u', 0, -2, []]]}
    cases['di_internal_future_eigenvariable'] = {'goal': dgoal,
        'proof': ['i', dgoal, 0, R(['s', -2])]}
    cases['false_equation_relabelled_truth'] = {'goal': ['=', 0, one], 'proof': R(0)}
    return cases


def extra_positives():
    cases = {}
    I, op = suite.I, suite.op
    one = ['s', 0]
    witness = I(one, 0, ['s', 1])
    term = I(1, 2, I(1, ['s', 3], ['s', 2]))
    matrix = ['=', term, term]
    body = op(matrix, witness, 1)
    target = op(body, ['s', -1])
    cases['capture_avoiding_nested_iterator_witness'] = {
        'goal': ['d', matrix], 'proof': ['i', ['d', matrix], witness, ['r', target[1]]],
    }
    # The inner iterator binds a variable of its own. The outer witness must
    # remain internally bound when it is inserted below both iterator binders.
    inner = ['d', matrix]
    outer = ['d', inner]
    cases['capture_avoiding_nested_formula_assumption'] = {
        'goal': outer,
        'proof': ['i', outer, witness, ['u', 0, witness, ['r', 0]]],
    }
    b = suite.Builder('step')
    matrix = ['=', I(1, 2, 3), 2]
    body = op(matrix, witness, 1)
    base = op(body, 0)
    old = b.use_equation(0, 0, b.refl(0), base[1], base[2])
    computation = b.comp(-1, witness, witness)
    step = b.trans(computation, old)
    cases['capturing_witness_with_used_local_fact'] = {
        'goal': ['d', matrix], 'proof': ['i', ['d', matrix], witness, step[2]],
    }
    return cases


def value(term, free, bound):
    if type(term) is int:
        return 0 if term == 0 else free[-term - 1] if term < 0 else bound[-term]
    if term[0] == 's':
        return value(term[1], free, bound) + 1
    result = value(term[2], free, bound)
    for _ in range(value(term[1], free, bound)):
        result = value(term[3], free, bound + [result])
    return result


def semantic_opening_checks():
    rng = random.Random(20261111)

    def tree(depth, fuel):
        variables = [0, -1, -2] + list(range(1, depth + 1))
        if fuel == 0 or rng.random() < 0.4:
            return rng.choice(variables)
        if rng.random() < 0.4:
            return ['s', tree(depth, fuel - 1)]
        counter = rng.choice([['s', 0], ['s', ['s', 0]], -1])
        return ['i', counter, tree(depth, fuel - 1), tree(depth + 1, fuel - 1)]

    checks = 0
    for depth in range(3):
        for _ in range(700):
            term, image = tree(depth + 1, 4), tree(0, 3)
            if not horn.term(term, 2, depth + 1) or not horn.term(image, 2):
                raise AssertionError('Generator escaped its declared scope')
            result = horn.opening(term, image, depth)
            if not horn.term(result, 2, depth):
                raise AssertionError('Opening escaped scope')
            free = [rng.randrange(3), rng.randrange(3)]
            locals_ = [rng.randrange(3) for _ in range(depth)]
            expected = value(term, free, [value(image, free, [])] + locals_)
            if value(result, free, locals_) != expected:
                raise AssertionError('Capture or substitution error')
            checks += 1
    # Opening a formula under an additional D leaves the two inner binders.
    matrix = ['d', ['=', 3, ['i', ['s', 0], 3, 1]]]
    image = ['i', ['s', 0], -1, 1]
    expected = ['d', ['=', image, ['i', ['s', 0], image, 1]]]
    if horn.opening(matrix, image) != expected:
        raise AssertionError('Opening captured a formula binder')
    checks += 1
    return checks


def main():
    output = ROOT / 'results'
    output.mkdir(exist_ok=True)
    examples = ROOT / 'examples'
    examples.mkdir(exist_ok=True)
    cases = suite.positive_fixtures('step') | extra_positives()
    results = []

    def record(name, path, certificate, expected):
        for optimized in (False, True):
            accepted = check(path, certificate, optimized)
            results.append({'case': name, 'checker': str(path.relative_to(ROOT)),
                            'optimized': optimized, 'expected': expected, 'accepted': accepted})

    for name, certificate in cases.items():
        target = translate.to_horn(certificate)
        returned = translate.to_control(target)
        repeated = translate.to_horn(returned)
        if target != repeated:
            raise AssertionError('Horn proof changed after the translation round trip')
        (examples / (name + '.json')).write_text(json.dumps(target, separators=(',', ':')) + '\n')
        for suffix, path, data in (
            ('source', ROOT / 'reference' / 'control.py', certificate),
            ('horn', ROOT / 'checker.py', target),
            ('backward', ROOT / 'reference' / 'control.py', returned),
        ):
            record(name + ':' + suffix, path, data, True)
    for name, certificate in suite.negative_fixtures().items():
        record('inherited:' + name, ROOT / 'reference' / 'control.py', certificate, False)
        adapted = copy.deepcopy(certificate)
        if 'proof' in adapted:
            adapted['proof'] = adapted_negative(adapted['proof'])
        record('adapted:' + name, ROOT / 'checker.py', adapted, False)
    for name, certificate in hard_negatives().items():
        record('additional:' + name, ROOT / 'checker.py', certificate, False)
    # Every filed source example is also covered explicitly, including byte
    # materialization rather than only the generator that produced it.
    filed = sorted((ROOT / 'reference').glob('*.json'))
    for path in filed:
        target = translate.to_horn(json.loads(path.read_text()))
        record('filed:' + path.name, ROOT / 'checker.py', target, True)
    semantic_checks = semantic_opening_checks()
    failures = [result for result in results if result['accepted'] != result['expected']]
    paths = [ROOT / 'reference' / 'control.py', ROOT / 'checker.py']
    report = {
        'baseline_commit': '443cff49563457a48ee0f663012d56c4bdb58fa0',
        'python': sys.version,
        'positive_source_certificates': len(cases),
        'filed_source_examples': len(filed),
        'inherited_negative_certificates': len(suite.negative_fixtures()),
        'additional_negative_certificates': len(hard_negatives()),
        'standalone_process_checks': len(results),
        'semantic_opening_checks': semantic_checks,
        'translation_round_trips': len(cases),
        'metrics': {str(path.relative_to(ROOT)): suite.metrics(path) for path in paths},
        'source_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in paths},
        'failures': failures,
        'results': results,
        'limitations': 'Finite regression and semantic checks supplement, and do not replace, the mathematical metatheorems.',
    }
    (output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'results'}, indent=2))
    return bool(failures)


if __name__ == '__main__':
    sys.exit(main())
