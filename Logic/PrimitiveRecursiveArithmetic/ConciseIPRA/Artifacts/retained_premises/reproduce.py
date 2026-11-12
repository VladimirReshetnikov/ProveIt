"""Reproduce complete-module measurements, provenance and certificate checks.

This script and the certificate compiler are untrusted support programs.
The standalone checkers import only Python's standard json library.
"""
import ast
import concurrent.futures
import csv
import gzip
import hashlib
import importlib.util
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
           tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    data = (ast.unparse(tree) + '\n').encode()
    return {'file': path.relative_to(ROOT).as_posix(),
            'tokens': sum(t.type not in IGNORED for t in tokenize.tokenize(io.BytesIO(data).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(data),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest()}


def verify_sources():
    rows = json.loads((ROOT / 'reference/PROVENANCE.json').read_text())['files']
    for row in rows:
        data = (ROOT / row['path']).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual != row['blob_sha']:
            raise ValueError('Frozen source differs: ' + row['path'])
    return len(rows)


def load_compiler():
    spec = importlib.util.spec_from_file_location('retained_compiler', ROOT / 'support/compile_retained.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_one(task):
    group, name, path, payload, expected, optimized = task
    command = [sys.executable, *(['-O'] if optimized else []), str(ROOT / path)]
    result = subprocess.run(command, input=payload, capture_output=True, timeout=30)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'group': group, 'case': name, 'checker': path, 'optimized': optimized,
            'expected': expected, 'accepted': accepted, 'exit_code': result.returncode,
            'passed': accepted == expected}


def main():
    EVIDENCE.mkdir(exist_ok=True)
    frozen = verify_sources()
    paths = sorted((ROOT / 'code').glob('*.py')) + sorted((ROOT / 'reference/checkers').glob('*.py'))
    rows = [measure(p) for p in paths]
    (EVIDENCE / 'metrics.json').write_text(json.dumps({'python': platform.python_version(),
        'normalization': 'ast.unparse(ast.parse(complete source)) followed by one LF',
        'records': rows}, indent=2) + '\n')
    with (EVIDENCE / 'metrics.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    tasks = []

    def add(group, name, path, payload, expected):
        for optimized in (False, True):
            tasks.append((group, name, path, payload, expected, optimized))

    local_cases = json.loads((ROOT / 'tests/local_cases.json').read_text())
    compiler = load_compiler()
    compiled = []
    for case in local_cases:
        source = ROOT / 'tests/local' / case['file']
        payload = source.read_bytes()
        for check in ('reference/checkers/canonical_516.py', 'code/checker_inferred_ast.py'):
            add('inferred-local', case['name'], check, payload, case['expected'])
        if case['expected']:
            output, stats = compiler.compile_certificate(json.loads(payload))
            encoded = json.dumps(output, separators=(',', ':')).encode() + b'\n'
            target = ROOT / 'tests/retained' / case['file']
            target.write_bytes(encoded)
            if output[-1] != json.loads(payload)[-1]:
                raise ValueError('The compiler changed the public goal')
            compiled.append({'case': case['name'], 'goal_unchanged': True,
                             'input_bytes': len(payload), 'output_bytes': len(encoded), 'stats': stats})
            for check in ('code/checker_retained_bytes.py', 'code/readable_retained.py'):
                add('retained-compiled', case['name'], check, encoded, True)
            add('retained-strict', case['name'], 'code/checker_retained_strict.py', encoded, case['public_goal'])
        else:
            for check in ('code/checker_retained_bytes.py', 'code/readable_retained.py', 'code/checker_retained_strict.py'):
                add('retained-negative', case['name'], check, payload, False)

    positives = ('compound_case', 'compound_implication', 'computation_successor',
        'computation_zero', 'guarded_induction', 'guarded_lift', 'guarded_literal',
        'transport_reflexivity', 'unguarded_progressive', 'zero_transport')
    for path in sorted((ROOT / 'tests/global').glob('*.json')):
        expected = path.name.startswith(positives)
        for check in ('reference/checkers/kernel_refinement_checker_tokens.py', 'code/checker_inferred_tokens.py'):
            add('inferred-global', path.name, check, path.read_bytes(), expected)

    for path in sorted((ROOT / 'tests/collision_controls').glob('*_old.json')):
        payload = path.read_bytes()
        add('collision-old', path.name, 'reference/checkers/canonical_516.py', payload, True)
        add('collision-untranslated', path.name, 'code/checker_retained_bytes.py', payload, False)
        output, stats = compiler.compile_certificate(json.loads(payload))
        if not stats['computation_collisions']:
            raise ValueError('Collision repair was not exercised')
        name = path.name.replace('_old.json', '.json')
        data = json.dumps(output, separators=(',', ':')).encode() + b'\n'
        (ROOT / 'tests/retained' / name).write_bytes(data)
        compiled.append({'case': name, 'goal_unchanged': output[-1] == json.loads(payload)[-1],
                         'input_bytes': len(payload), 'output_bytes': len(data), 'stats': stats})
        for check in ('code/checker_retained_bytes.py', 'code/readable_retained.py', 'code/checker_retained_strict.py'):
            add('collision-repaired', name, check, data, True)

    for name, candidate_expected in [('inferred_major_overrides_padding.json', True),
                                      ('inferred_major_requires_proof.json', False)]:
        payload = (ROOT / 'tests' / name).read_bytes()
        add('inferred-new-protocol', name, 'reference/checkers/canonical_516.py', payload, False)
        add('inferred-new-protocol', name, 'code/checker_inferred_ast.py', payload, candidate_expected)

    valid = json.loads((ROOT / 'tests/retained/computation_zero_local.json').read_text())
    bad_prefixes = [None, True, False, 0.0, 1.0, '0', [], {}, [1.5], [True], ['[]'], {'k': 0}]
    for j, prefix in enumerate(bad_prefixes):
        data = json.dumps([prefix, *valid], separators=(',', ':')).encode()
        # [] is the sole exact integer/list prefix in this list and is unused.
        add('strict-certificate-types', str(j), 'code/checker_retained_strict.py', data, prefix == [] and type(prefix) is list)
    for j, goal in enumerate([0, [], None, True, [0], [0, 1], [0, 2], [-2, -2], [0, 0.0], [[0, 0]]]):
        data = json.dumps([goal]).encode()
        add('strict-public-grammar', str(j), 'code/checker_retained_strict.py', data, False)

    # Native validator is an independent exact acceptance refinement.
    native_cases = [(p.name, p.read_bytes()) for p in sorted((ROOT / 'tests/native').glob('*.json'))]
    native_cases += [('local_' + c['file'], (ROOT / 'tests/local' / c['file']).read_bytes()) for c in local_cases]
    for a in (-20, -4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 20):
        for goal in ([a, a], [[a], a], [[[0, a, 0], a]]):
            native_cases.append(('scope_' + repr(goal), json.dumps([goal]).encode()))
    native_cases.append(('fresh_scope_regression', b'[[0,0,[-1],0],[0,0,0,0],[[[0,5,0],3]]]'))
    # Preserve the independently audited expectations; these are raw-certificate
    # acceptance comparisons, rather than a claim that every native case is guarded.
    historical = json.loads((EVIDENCE / 'native_prefilter_validation.json').read_text())
    if len(native_cases) != historical['cases']:
        raise ValueError('Native fixture inventory changed')
    native_pairs = []
    for name, payload in native_cases:
        for opt in (False, True):
            native_pairs.append(('native-equivalence', name, 'reference/checkers/native_788.py', payload, False, opt))
            native_pairs.append(('native-equivalence', name, 'code/checker_native_validated.py', payload, False, opt))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run_one, tasks))
        native_results = list(pool.map(run_one, native_pairs))
    for a, b in zip(native_results[::2], native_results[1::2]):
        a['expected'] = b['expected'] = a['accepted']
        a['passed'] = True
        b['passed'] = a['accepted'] == b['accepted']
    results += native_results
    failures = [r for r in results if not r['passed']]
    summary = {'python': platform.python_version(), 'frozen_git_blobs': frozen,
               'checker_processes': len(results), 'passed': len(results) - len(failures),
               'failures': len(failures), 'compiled_certificates': len(compiled),
               'native_paired_comparisons': len(native_results) // 2,
               'claim': 'Finite implementation validation; mathematical equivalence uses the written proofs.'}
    (EVIDENCE / 'validation.json').write_text(json.dumps({'summary': summary, 'compilation': compiled,
        'results': results}, indent=2) + '\n')
    (EVIDENCE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
