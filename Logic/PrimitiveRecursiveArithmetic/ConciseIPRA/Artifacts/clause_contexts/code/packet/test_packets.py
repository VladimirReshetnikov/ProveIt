"""Regression and adversarial tests for the standalone packet checker."""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import translate


ROOT = Path(__file__).resolve().parent


def metrics(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    data = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(data.decode()).readline))
    return {'normalized_bytes': len(data), 'tokens': tokens,
            'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
            'source_bytes': path.stat().st_size,
            'source_gzip9_bytes': len(gzip.compress(path.read_bytes(), compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'normalized_sha256': hashlib.sha256(data).hexdigest()}


def run(path, certificate, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    process = subprocess.run(command, input=json.dumps(certificate), text=True,
                             capture_output=True, timeout=20)
    return process.returncode == 0 and process.stdout == 'ACCEPT\n'


def negative_cases(positives):
    truth = [0, 0]
    one = [0]
    false = [0, one]
    D = ['d', [1, 1]]
    cases = {}
    for name, goal in [('boolean_term', [False, False]), ('float_term', [0.0, 0.0]),
                       ('string_term', ['0', '0']), ('mapping_term', [{}, {}]),
                       ('null_term', [None, None]), ('free_negative', [-1, -1]),
                       ('free_positive', [1, 1]), ('wrong_formula_length', [0, 0, 0]),
                       ('empty_formula', []), ('bad_binder_matrix', ['d', 'd']),
                       ('bad_successor_length', [[0, 0], [0, 0]]),
                       ('raw_zero_iterator', [[0, 0, 1], [0, 0, 1]]),
                       ('iterator_body_escape', [[[0], 0, 2], [[0], 0, 2]])]:
        cases['public_' + name] = [goal]
    for name, data in [('object', {}), ('string', ''), ('null', None), ('scalar', 0), ('empty', [])]:
        cases['top_' + name] = data
    cases['missing_false_equation_proof'] = [false]
    cases['unused_packet_before_reflexivity'] = [[0, 0], truth]
    cases['extra_field_in_packet'] = [[-1, 0, 0], D]
    cases['short_packet'] = [[-1], D]
    cases['nonpacket_string'] = ['xx', D]
    cases['nonpacket_mapping'] = [{'a': 0, 'b': 0}, D]
    for name, marker in [('negative', -2), ('boolean', True), ('float', -1.0),
                          ('high_clause', 9), ('absent_clause', 0)]:
        cases['marker_' + name] = [[marker, 0], D]
    for name, witness in [('future_variable', -1), ('bound_variable', 1), ('boolean', False),
                           ('mapping', {}), ('zero_iterator', [0, 0, 1])]:
        cases['close_witness_' + name] = [[-1, witness], D]
    cases['close_equation_goal'] = [[-1, 0], false]
    cases['malformed_step_major'] = [[[True, True], truth], false]
    cases['malformed_step_minor'] = [[truth, [False, False]], false]
    cases['step_root_fallback'] = [[truth, truth], false]
    cases['step_successor_instead_of_iterator'] = [[truth, [one, one]], false]
    cases['step_wrong_predecessor'] = [
        [[one, one], [[[0], 0, 1], [[0], 0, 1]]], [[[0], 0, 1], 0],
    ]
    # Choose accepted proofs actually containing each packet type, then corrupt
    # a field whose rejection is forced by its documented input contract.
    found = {}
    for name, certificate in positives.items():
        for index, (major, data) in enumerate(certificate[:-1]):
            kind = 'use' if type(major) is int and major >= 0 else 'close' if major == -1 else 'open' if major[0] == 'd' else 'step'
            found.setdefault(kind, (name, certificate, index))
    for kind, (name, certificate, index) in found.items():
        cases[kind + '_trailing_packet'] = [[0, 0]] + copy.deepcopy(certificate)
        bad = copy.deepcopy(certificate)
        if kind == 'open':
            bad[index][1] = False
            cases['open_boolean_placeholder'] = bad
            bad = copy.deepcopy(certificate)
            bad[index][1] = one
            cases['open_nonzero_placeholder'] = bad
        elif kind == 'step':
            bad[index][1] = [None, None]
            cases['step_invalid_intermediate_formula'] = bad
        else:
            bad[index][1] = -1000000
            cases[kind + '_distant_future_witness'] = bad
            bad = copy.deepcopy(certificate)
            bad[index][1] = 1
            cases[kind + '_unbound_positive_witness'] = bad
            if kind == 'use':
                bad = copy.deepcopy(certificate)
                bad[index][0] = 1000000
                cases['use_out_of_range_context'] = bad
    return cases


def semantic_checks():
    rng = random.Random(20261111)

    def tree(depth, fuel):
        if fuel == 0 or rng.random() < 0.4:
            return rng.choice([0, -1, -2] + list(range(1, depth + 1)))
        if rng.random() < 0.4:
            return [tree(depth, fuel - 1)]
        return [rng.choice([[0], [[0]], -1]), tree(depth, fuel - 1), tree(depth + 1, fuel - 1)]

    def value(a, free, bound):
        if type(a) is int:
            return 0 if a == 0 else free[-a - 1] if a < 0 else bound[-a]
        if len(a) == 1:
            return value(a[0], free, bound) + 1
        result = value(a[1], free, bound)
        for _ in range(value(a[0], free, bound)):
            result = value(a[2], free, bound + [result])
        return result

    checks = 0
    for depth in range(3):
        for _ in range(700):
            term, image = tree(depth + 1, 4), tree(0, 3)
            result = translate.packet.opening(term, image, depth)
            if not translate.packet.term(result, 2, depth):
                raise AssertionError('Opening escaped scope')
            free = [rng.randrange(3), rng.randrange(3)]
            bound = [rng.randrange(3) for _ in range(depth)]
            if value(result, free, bound) != value(term, free, [value(image, free, [])] + bound):
                raise AssertionError('Opening changed the substitution meaning')
            checks += 1
    image = [[0], -1, 1]
    formula = ['d', [3, [[0], 3, 1]]]
    if translate.packet.opening(formula, image) != ['d', [image, [[0], image, 1]]]:
        raise AssertionError('Formula opening captured a variable')
    return checks + 1


def main():
    results = []
    positives = {}
    examples = ROOT / 'examples'
    examples.mkdir(exist_ok=True)
    result_dir = ROOT / 'results'
    result_dir.mkdir(exist_ok=True)

    def record(name, filename, certificate, expected):
        for optimized in (False, True):
            accepted = run(ROOT / filename, certificate, optimized)
            results.append({'case': name, 'checker': filename, 'optimized': optimized,
                            'expected': expected, 'accepted': accepted})

    sources = sorted((ROOT / 'reference' / 'certificates').glob('*.json'))
    for source in sources:
        explicit = json.loads(source.read_text())
        target = translate.to_packets(explicit)
        backward = translate.to_explicit(target)
        if translate.to_packets(backward) != target:
            raise AssertionError('Packet round trip changed a certificate')
        positives[source.stem] = target
        (examples / source.name).write_text(json.dumps(target, separators=(',', ':')) + '\n')
        record(source.stem + ':packet', 'checker.py', target, True)
        record(source.stem + ':original', 'reference/control_recursive.py', explicit, True)
        record(source.stem + ':decoded', 'reference/control_recursive.py', backward, True)
    negatives = negative_cases(positives)
    for name, certificate in negatives.items():
        record(name, 'checker.py', certificate, False)
    semantic = semantic_checks()
    sample = positives['induction_uses_hypothesis']
    (examples / 'induction_uses_hypothesis.txt').write_text(translate.format_packets(sample))
    failures = [row for row in results if row['accepted'] != row['expected']]
    paths = ['checker.py', 'checker_empty_antecedent.py', 'checker_ranked.py',
             'reference/control_recursive.py']
    report = {'python': sys.version,
              'positive_certificates': len(positives),
              'negative_certificates': len(negatives),
              'standalone_process_checks': len(results),
              'exact_packet_round_trips': len(positives),
              'semantic_opening_checks': semantic,
              'metrics': {path: metrics(ROOT / path) for path in paths},
              'failures': failures, 'results': results,
              'limits': 'Finite tests supplement the structural packet translation and scope proofs; they do not prove the interpretation theorem.'}
    (result_dir / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'results'}, indent=2))
    return bool(failures)


if __name__ == '__main__':
    sys.exit(main())
