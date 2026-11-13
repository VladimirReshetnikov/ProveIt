"""Offline, independent process and public-grammar checks.

This development harness is not part of the trusted checker. Its finite
tests do not prove universal soundness or completeness.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import ast
import copy
import gzip
import hashlib
import io
import json
import platform
import random
import subprocess
import sys
import tokenize

from compile_examples import compile_all

ROOT = Path(__file__).resolve().parent
OMIT = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(relative):
    raw = (ROOT / relative).read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + '\n').encode()
    return {'path': relative,
            'tokens': sum(t.type not in OMIT for t in tokenize.tokenize(io.BytesIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized),
            'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def run(job):
    relative, case, expected, optimized = job
    process = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(ROOT / relative)],
                             input=json.dumps(case['certificate']), text=True,
                             capture_output=True, timeout=20)
    accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
    return {'profile': relative, 'case': case['name'], 'optimized': optimized,
            'expected': expected, 'accepted': accepted, 'exit_code': process.returncode,
            'pass': accepted == expected}


def load_cases(relative):
    data = json.loads((ROOT / relative).read_text())
    return data['cases'] if isinstance(data, dict) else data


def true_alias(tree):
    if type(tree) is list:
        return [true_alias(x) for x in tree]
    return True if tree == 1 else tree


def extra_cases(base, induction, exact):
    cases = []
    def add(name, document, accepted, strict=None):
        cases.append({'name': name, 'certificate': document, 'expected': accepted,
                      'strict_expected': accepted if strict is None else strict})
    opaque = [None, True, False, 1.5, '', {}, 'unused', float('nan'),
              float('inf'), float('-inf'), {'unused': ['arbitrary', None, 0.25]}]
    for n, value in enumerate(opaque):
        add('opaque_prefix_zero_' + str(n), [value] + copy.deepcopy(base), True, False)
    add('opaque_prefix_used_induction', [{'irrelevant': ['data', None]}] + copy.deepcopy(induction), True, False)
    add('public_true_aliases', base[:-1] + [true_alias(base[-1])], True, False)
    invalid = [False, 0, 2, 3, -1, 0.0, 1.0, 1.5, float('nan'),
               float('inf'), float('-inf'), None, '', 'x', {}, []]
    for n, value in enumerate(invalid):
        goal = copy.deepcopy(base[-1])
        goal[1] = value
        add('used_public_leaf_' + str(n), base[:-1] + [goal], False)
    for n, value in enumerate([None, '', 'x', {}, {'three': 3}, False, 1.0]):
        add('bad_consumed_packet_' + str(n), base[:-2] + [value] + base[-1:], False)
    add('used_float_computation_spelling', [[0, 1.0, 1.0], [[1, 1, 1], 1]], True, False)
    add('empty_document', [], False)
    add('scalar_document', 0, False)
    add('object_document', {}, False)
    add('false_zero_one', base[:-1] + [[1, [1]]], False)
    add('false_one_zero', base[:-1] + [[[1], 1]], False)
    if exact:
        # These would refer to administrative padding positions in the old
        # encoding. The actual-binder grammar rejects them.
        for n, goal in enumerate([[[3], [1]], [[5], [1]], [[1, 3, 1], 1], [[1, 1, 5], 1]]):
            add('dummy_slot_rejection_' + str(n), base[:-1] + [goal], False)
    return cases


def exact_term(tree, variables):
    if tree is True:
        return True
    if type(tree) is int:
        return tree == 1 or (tree >= 3 and tree % 2 == 1 and (tree - 3) // 2 < variables)
    if type(tree) is not list:
        return False
    if len(tree) == 1:
        return exact_term(tree[0], variables)
    if len(tree) == 3:
        n, a, h = tree
        return exact_term(n, variables) and exact_term(a, variables) and exact_term(h, variables + 1)
    return False


def exact_formula(tree, variables=0):
    if type(tree) is not list:
        return False
    if len(tree) == 1:
        return exact_formula(tree[0], variables + 2)
    if len(tree) == 2:
        return exact_term(tree[0], variables) and exact_term(tree[1], variables)
    return False


def check_exact_grammar():
    module = ast.parse((ROOT / 'code/checker_exact.py').read_text())
    assignment = next(n for n in module.body if isinstance(n, ast.Assign)
                      and any(isinstance(t, ast.Name) and t.id == 'i' for t in n.targets))
    env = {'k': 0}
    exec(compile(ast.Module(body=[assignment], type_ignores=[]), '<isolated-public-traversal>', 'exec'), env)
    opener = env['i']
    rng = random.Random(20261113)
    leaves = [-3, -1, 0, 1, 2, 3, 5, 7, 9, 17, True, False, 1.0, 1.5, None, '', 'x', {}]
    def raw(depth):
        if not depth or rng.random() < 0.5:
            return copy.deepcopy(rng.choice(leaves))
        return [raw(depth - 1) for _ in range(rng.randrange(5))]
    samples = [raw(5) for _ in range(2500)]
    # Directed scope boundaries, together with both term constructors and D.
    for binders in range(7):
        for index in range(-2, 4 * binders + 12):
            for term in (index, [index], [1, index, 3], [1, 1, index]):
                goal = [term, 1]
                for _ in range(binders):
                    goal = [goal]
                samples.append(goal)
    samples.extend(row['certificate'][-1] for row in load_cases('fixtures/exact_positives.json'))
    mismatches = []
    for index, goal in enumerate(samples):
        expected = exact_formula(goal)
        try:
            result = opener(goal)
            accepted = True
        except Exception:
            result = None
            accepted = False
        if accepted != expected or accepted and result != goal:
            mismatches.append({'index': index, 'goal': goal, 'expected': expected,
                               'accepted': accepted, 'result': result})
    return {'comparisons': len(samples), 'mismatches': mismatches,
            'oracle': 'Native Eq/D syntax with genuine binder count; true aliases numerical-zero code 1.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metrics-only', action='store_true')
    args = parser.parse_args()
    profiles = ['code/checker_sorted.py', 'code/checker_exact.py', 'controls/strict300.py',
                'controls/intrinsic_unfused.py', 'controls/exact_unfused.py',
                'controls/exact_nodes361.py', 'controls/exact_intrinsic591.py',
                'controls/exact_nodes358.py', 'controls/checker_ast337.py',
                'controls/checker_tokens299.py', 'controls/checker_bytes575.py']
    metrics = [measure(p) for p in profiles]
    result = {'python': platform.python_version(), 'metrics': metrics}
    if not args.metrics_only:
        inherited = load_cases('fixtures/inherited112.json')
        exact = load_cases('fixtures/exact_positives.json')
        compiled = compile_all()
        frozen = {r['name']: r['certificate'] for r in exact}
        compilation_matches = all(frozen[r['name']] == r['certificate'] for r in compiled) and len(compiled) == len(exact)
        if not compilation_matches:
            raise AssertionError('Canonical compiler did not reproduce the frozen exact fixtures')
        sorted_base = next(c['certificate'] for c in inherited if c['name'] == 'direct_zero')
        sorted_induction = next(c['certificate'] for c in inherited if c['name'] == 'guarded_induction_with_used_hypothesis_local')
        exact_base = next(c['certificate'] for c in exact if c['name'] == 'direct_zero')
        exact_induction = next(c['certificate'] for c in exact if c['name'] == 'guarded_induction_with_used_hypothesis_local')
        sorted_extra = extra_cases(sorted_base, sorted_induction, False)
        exact_extra = extra_cases(exact_base, exact_induction, True)
        capture = json.loads((ROOT / 'fixtures/exact_future_witness_capture.json').read_text())
        exact_extra.append({'name': 'exact_future_witness_capture', 'certificate': capture, 'expected': False})
        for c in exact:
            for label, false in [('zero_one', [1, [1]]), ('one_zero', [[1], 1])]:
                exact_extra.append({'name': c['name'] + '_false_' + label,
                                    'certificate': c['certificate'][:-1] + [false], 'expected': False})
        jobs = []
        for c in inherited:
            for p in ('code/checker_sorted.py', 'controls/intrinsic_unfused.py', 'controls/strict300.py'):
                for opt in (False, True):
                    jobs.append((p, c, c['expected'], opt))
        for c in sorted_extra:
            for p in ('code/checker_sorted.py', 'controls/intrinsic_unfused.py', 'controls/strict300.py'):
                expected = c['strict_expected'] if p == 'controls/strict300.py' else c['expected']
                for opt in (False, True):
                    jobs.append((p, c, expected, opt))
        for c in exact + exact_extra:
            for p in ('code/checker_exact.py', 'code/checker_readable.py', 'controls/exact_unfused.py'):
                for opt in (False, True):
                    jobs.append((p, c, c['expected'], opt))
        # Independently rerun the source protocol on its own canonical proofs.
        exact_control = [c for c in load_cases('fixtures/exact_control_cases.json') if c['expected']]
        for c in exact_control:
            for opt in (False, True):
                jobs.append(('controls/exact_nodes361.py', c, True, opt))
        with ThreadPoolExecutor(max_workers=4) as pool:
            runs = list(pool.map(run, jobs))
        failures = [r for r in runs if not r['pass']]
        grammar = check_exact_grammar()
        result.update({'inherited_cases': len(inherited), 'exact_canonical_proofs': len(exact),
                       'sorted_extra_cases': len(sorted_extra), 'exact_extra_cases': len(exact_extra),
                       'compiler_reproduction_matches': compilation_matches,
                       'process_executions': len(runs), 'failures': failures,
                       'grammar': grammar, 'results': runs,
                       'limits': ['Finite regressions are supporting evidence, not universal soundness proofs.',
                                  'The sorted companion has canonical completeness; its admitted padding aliases are not all covered.',
                                  'The exact checker validates genuine numerical binders and Eq/D syntax, with true as an alias for code 1.',
                                  'Unused payload objects are deliberately not alphabet-validated.']})
    (ROOT / 'evidence').mkdir(exist_ok=True)
    destination = 'evidence/metrics_reproduced.json' if args.metrics_only else 'evidence/reproduction.json'
    (ROOT / destination).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}, indent=2))
    if result.get('failures') or result.get('grammar', {}).get('mismatches'):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
