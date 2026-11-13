"""Independent replay, exact proof translations, adversarial and CLI checks."""
from pathlib import Path
import argparse
import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
import random
import subprocess
import sys
import tokenize

import macros as m
import reference_kernel as ref
import convert
import control_translations as ct

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def expect_rejected(checker, certificate):
    try:
        checker.check(certificate)
    except Exception:
        return
    raise AssertionError('invalid certificate accepted')


def metrics(path):
    source = Path(path).read_text()
    tree = ast.parse(source)
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and type(tree.body[0].value.value) is str):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in excluded for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline))
    return {'normalized_bytes': len(normalized), 'significant_tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(normalized, 9, mtime=0)),
            'source_sha256': hashlib.sha256(source.encode()).hexdigest()}


def cases():
    positive = {p.stem: json.loads(p.read_text()) for p in sorted((HERE / 'examples').glob('*.json'))}
    negative = {}
    def add(name, goal, proof):
        negative[name] = {'goal': goal, 'proof': proof}
    add('false_equation', [0, m.ONE], ['u', 0, 0, []])
    add('unknown_rule', [0, 0], ['unknown'])
    add('missing_use_field', [0, 0], ['u', 0, 0])
    add('extra_use_field', [0, 0], ['u', 0, 0, [], 0])
    add('boolean_clause_index', [0, 0], ['u', False, 0, []])
    add('negative_clause_index', [0, 0], ['u', -1, 0, []])
    add('nonexistent_clause', [0, 0], ['u', 1, 0, []])
    add('free_goal', [-1, -1], ['u', 0, -1, []])
    add('loose_bound_goal', [1, 1], ['u', 0, 0, []])
    add('loose_D_bound', [[3, 3]], ['i', 0, ['u', 0, 0, []]])
    add('boolean_numeral', [False, False], ['u', 0, False, []])
    add('boolean_successor_tag', [[False, 0], [False, 0]], ['u', 0, [False, 0], []])
    add('nonzero_successor_tag', [[1, 0], [1, 0]], ['u', 0, [1, 0], []])
    add('float_numeral', [0.0, 0.0], ['u', 0, 0.0, []])
    add('string_numeral', ['0', '0'], ['u', 0, '0', []])
    add('empty_formula', [], ['u', 0, 0, []])
    add('dict_formula', {'a': 0}, ['u', 0, 0, []])
    add('noncanonical_zero_iterator', [[0, 0, 1], [0, 0, 1]], ['u', 0, [0, 0, 1], []])
    add('noncanonical_successor_iterator', [[m.ONE, 0, 1], [m.ONE, 0, 1]],
        ['u', 0, [m.ONE, 0, 1], []])
    add('malformed_erased_update', [[0, 0, 999], [0, 0, 999]],
        ['u', 0, [0, 0, 999], []])
    add('atomic_intro_goal', [0, 0], ['i', 0, ['u', 0, 0, []]])
    truth = m.D([0, 0])
    add('intro_out_of_scope_witness', truth, ['i', -1, ['u', 0, 0, []]])
    add('intro_noncanonical_zero_witness', truth, ['i', [0, 0, 1], ['u', 0, 0, []]])
    add('intro_boolean_witness', truth, ['i', False, ['u', 0, 0, []]])
    ordinary = copy.deepcopy(positive['ordinary_elimination_self_target'])
    wrong = copy.deepcopy(ordinary)
    wrong['proof'][5] = ['u', 0, 0, []]
    negative['wrong_equality_source'] = wrong
    wrong = copy.deepcopy(ordinary)
    wrong['proof'][3] = -2
    negative['escaping_equality_target'] = wrong
    wrong = copy.deepcopy(ordinary)
    wrong['proof'][2] = [-2, -2]
    wrong['proof'][6] = ['u', 0, -2, []]
    negative['branch_scope_escape'] = wrong
    wrong = copy.deepcopy(ordinary)
    wrong['proof'][4] = ['u', 1, 0, []]
    negative['branch_clause_leaks_into_major'] = wrong
    wrong = copy.deepcopy(ordinary)
    wrong['proof'][1] = 0
    negative['nonformula_major_matrix'] = wrong
    wrong = copy.deepcopy(ordinary)
    wrong['proof'][3] = [0, 0, 999]
    negative['invalid_target_hidden_by_normalization'] = wrong
    # Direct mode forgery: this matrix's zero instance is0=1 but its progress
    # hypothesis at a fresh variable is C(z,0,0)=1, not0=1.
    case_goal = m.D([m.C(m.Y, 0, m.X), m.ONE])
    add('zero_witness_wrong_mode', case_goal, ['i', 0, ['u', 1, 0, []]])
    # The false claim tries to turn the eliminated b into a D-bound variable.
    name_zero = [[[1, 0, 3], 0]]
    inner = [[[1, 0, -1], 0]]
    bad_goal = [[[1, 0, 2], 0]]
    add('compound_eigenparameter_capture', bad_goal,
        ['e', name_zero[0], inner, -1,
         ['i', 0, ['u', 0, 0, []]], ['u', 0, -1, []],
         ['i', m.ONE, ['u', 1, m.ONE, ['u', 0, 0, []]]]])
    negative['extra_document_field'] = {'goal': [0, 0], 'proof': ['u', 0, 0, []], 'extra': 1}
    negative['missing_goal'] = {'proof': ['u', 0, 0, []]}
    negative['missing_proof'] = {'goal': [0, 0]}
    negative['array_document'] = []
    # Explicitly valid contract cases: unconditional clause payloads are unused.
    positive['unconditional_null_payload'] = {'goal': [0, 0], 'proof': ['u', 0, 0, None]}
    positive['unconditional_object_payload'] = {'goal': [0, 0], 'proof': ['u', 0, 0, {'unused': 1}]}
    return positive, negative


def evaluator(term, free, bound=()):
    if type(term) is int:
        return 0 if term == 0 else bound[term - 1] if term > 0 else free[-term - 1]
    if len(term) == 2:
        return evaluator(term[1], free, bound) + 1
    counter, seed, update = term
    n = evaluator(counter, free, bound)
    r = evaluator(seed, free, bound)
    if n > 10000:
        raise ValueError('semantic test budget')
    for _ in range(n):
        r = evaluator(update, free, (r,) + tuple(bound))
    return r


def normalization_checks(checker):
    rng = random.Random(20261111)
    def term(depth, size):
        leaves = [0, -1, -2] + list(range(1, depth + 1))
        if size == 0 or rng.randrange(4) == 0:
            return rng.choice(leaves)
        if rng.randrange(3) == 0:
            return [0, term(depth, size - 1)]
        counter = rng.choice(leaves + [m.ONE, m.TWO])
        return [counter, term(depth, size - 1), term(depth + 1, size - 1)]
    syntax_count = semantic_count = opening_count = 0
    for _ in range(220):
        a = term(0, 3)
        ref.raw_term(a, 2)
        expected = ref.normal(a)
        got = checker.walk(a, lambda i, d: i)
        require(got == expected, 'normal form disagreement')
        require(ref.normal(expected) == expected, 'normalizer not idempotent')
        syntax_count += 1
        for free in [(0, 0), (1, 2), (2, 1)]:
            require(evaluator(a, free) == evaluator(expected, free), 'numerical semantics changed')
            semantic_count += 1
        a = term(1, 2)
        t = ref.normal(term(0, 1))
        expected = ref.opening(a, t)
        require(checker.sub(a, t) == expected, 'capture-avoiding opening differs')
        for free in [(0, 1), (2, 1)]:
            require(evaluator(expected, free) == evaluator(a, free, (evaluator(t, free),)),
                    'opening semantics differs')
            opening_count += 1
    capture = [m.ONE, m.ONE, [m.ONE, 1, [2, 0, 2]]]
    require(checker.walk(capture, lambda i, d: i) == m.ONE, 'nested capture regression')
    return {'normal_forms': syntax_count + 1, 'numerical_evaluations': semantic_count,
            'opening_semantics': opening_count, 'skipped': 0}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--checker', type=Path, default=ROOT / 'code/checker.py')
    parser.add_argument('--control', type=Path, default=ROOT / 'code/control_separate.py')
    parser.add_argument('--forward', type=Path, default=HERE / 'forward_kernel.py')
    args = parser.parse_args()
    checker = load('selected_validation', args.checker)
    forward = load('forward_validation', args.forward)
    control = load('control_validation', args.control)
    positive, negative = cases()
    evidence = {'python': sys.version, 'accepted': [], 'rejected': [], 'translations': []}
    control_dir = HERE / 'control_examples'
    control_dir.mkdir(exist_ok=True)
    for name, data in positive.items():
        checker.check(data)
        replay = convert.certificate_from_selected(data)
        forward.check(replay)
        reconstructed = convert.certificate_to_selected(replay)
        checker.check(reconstructed)
        require(reconstructed['goal'] == data['goal'], 'roundtrip goal mismatch')
        old_proof = ct.fusion_to_control(replay['proof'])
        old = {'goal': data['goal'], 'proof': old_proof}
        ref.check(old, True)
        control_goal = {'goal': data['goal'], 'proof': ct.control_to_selected(old_proof)}
        control.check(control_goal)
        (control_dir / (name + '.json')).write_text(json.dumps(control_goal, indent=2) + '\n')
        restored = {'goal': data['goal'], 'proof': ct.control_to_fusion(old_proof)}
        ref.check(restored)
        forward.check(restored)
        checker.check(convert.certificate_to_selected(restored))
        evidence['accepted'].append(name)
        evidence['translations'].append({'name': name, 'exact_goal': True,
                                         'selected_four_roundtrip': True,
                                         'separate_rule_control_roundtrip': True})
    invalid_dir = HERE / 'reject_examples'
    invalid_dir.mkdir(exist_ok=True)
    for name, data in negative.items():
        expect_rejected(checker, data)
        (invalid_dir / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
        evidence['rejected'].append(name)
    cli = []
    for optimized in [False, True]:
        command = [sys.executable] + (['-O'] if optimized else []) + [str(args.checker)]
        for expected, collection in [(True, positive), (False, negative)]:
            for name, data in collection.items():
                done = subprocess.run(command, input=json.dumps(data), text=True,
                                      capture_output=True, timeout=30)
                require(done.returncode == (0 if expected else 1), 'CLI status ' + name)
                require(done.stdout.strip() == ('ACCEPT' if expected else 'REJECT'), 'CLI output ' + name)
                cli.append({'name': name, 'optimized': optimized, 'accepted': expected})
        for raw in ['', '{', 'null', 'true', '0', '"certificate"', '{"goal":NaN,"proof":[]}']:
            done = subprocess.run(command, input=raw, text=True, capture_output=True, timeout=30)
            require(done.returncode == 1 and done.stdout.strip() == 'REJECT', 'malformed JSON')
            cli.append({'malformed_document': raw, 'optimized': optimized, 'accepted': False})
    evidence['cli_checks'] = len(cli)
    evidence['cli_results'] = cli
    evidence['normalization'] = normalization_checks(checker)
    open_data = json.loads((HERE / 'open_parameter_sequent.json').read_text())
    require(ref.derive(open_data['proof'], open_data['context'], open_data['scope']) == open_data['goal'],
            'open independent replay')
    require(forward.derive(open_data['proof'], open_data['context'], open_data['scope']) == open_data['goal'],
            'open forward replay')
    evidence['open_sequent_checks'] = 1
    evidence['metrics'] = {'selected': metrics(args.checker),
                           'matched_separate_rules': metrics(args.control)}
    (HERE / 'verification.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({'accepted': len(positive), 'rejected': len(negative),
                      'exact_roundtrips': len(evidence['translations']),
                      'cli_checks': len(cli), 'normalization': evidence['normalization'],
                      'metrics': evidence['metrics']}, indent=2))


if __name__ == '__main__':
    main()
