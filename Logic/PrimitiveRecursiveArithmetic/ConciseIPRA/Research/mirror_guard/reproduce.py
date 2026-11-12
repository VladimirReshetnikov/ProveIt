"""Rebuild certificates, check representative proofs/attacks, and measure code.

Python 3.12.14 is the pinned comparison runtime. No packages are required.
All selected checkers are standalone programs; this runner is untrusted.
"""
import ast
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CHECKERS = ['checker_ast.py', 'checker_bytes.py', 'checker_tokens.py',
            'readable_checker.py', 'strict_checker.py']


def check(checker, data, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(checker)]
    try:
        result = subprocess.run(command, input=data, capture_output=True,
                                text=True, timeout=30)
    except subprocess.TimeoutExpired:
        return False, 'timeout'
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return accepted, result.stderr[-600:]


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    class StripDocstrings(ast.NodeTransformer):
        def visit(self, node):
            node = super().visit(node)
            if isinstance(node, (ast.Module, ast.FunctionDef,
                                 ast.AsyncFunctionDef, ast.ClassDef)):
                if (node.body and isinstance(node.body[0], ast.Expr)
                        and isinstance(node.body[0].value, ast.Constant)
                        and isinstance(node.body[0].value.value, str)):
                    node.body = node.body[1:]
            return node
    tree = ast.fix_missing_locations(StripDocstrings().visit(tree))
    normalized = (ast.unparse(tree) + '\n').encode()
    omit = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in omit for t in
                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return {'file': str(path.relative_to(ROOT)), 'tokens': tokens,
            'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
            'normalized_bytes': len(normalized), 'raw_bytes': len(raw),
            'gzip9_normalized_bytes': len(gzip.compress(normalized, 9, mtime=0)),
            'gzip9_raw_bytes': len(gzip.compress(raw, 9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    generated = subprocess.run([sys.executable, str(ROOT / 'tests/mirrored_cases.py')],
                               capture_output=True, text=True, check=True)
    (evidence / 'build_cases.json').write_text(generated.stdout)
    cases = json.loads((evidence / 'cases.json').read_text())
    tests = []
    for case in cases:
        data = {scope: (ROOT / 'tests/certificates' / entry['name']).read_text()
                for scope, entry in case['files'].items()}
        tests.append({'name': case['name'], 'expected': case['expected'],
                      'data': data, 'audit': case['audit']})
    for row in json.loads((ROOT / 'tests/negative_controls.json').read_text()):
        data = json.dumps(row['packet']) + '\n'
        test = {'name': row['name'], 'expected': False,
                'data': {'local': data, 'global': data}}
        if row['name'] == 'inherited_induction_step_with_base_only_context':
            test['expected'] = True
            test['expected_by_checker'] = {'strict_checker.py': False}
            test['explanation'] = (
                'The old falsy case/progress mode is ignored. The equation root '
                'selects the genuine induction hypothesis, so the core accepts '
                'this valid Q_y(I(y,0;u.u)=0) theorem. The strict public-goal '
                'wrapper rejects its Q root, which is a clause resource rather '
                'than a canonical Eq/D object formula.')
        tests.append(test)
    for path in sorted((ROOT / 'reference/attacks').glob('*.json')):
        data = path.read_text()
        tests.append({'name': path.stem, 'expected': False,
                      'data': {'local': data, 'global': data}})

    # The falsy mode field no longer selects atomic cases versus progress.
    # Change every DI marker in a known proof to the other old spelling.
    mirror = next(c for c in cases if c['name'] == 'mirror_DI_two')
    data = {}
    for scope, entry in mirror['files'].items():
        packet = json.loads((ROOT / 'tests/certificates' / entry['name']).read_text())
        for command in packet[:-1]:
            if not command[0] and not command[2]:
                command[2] = [] if command[2] == 0 else 0
        data[scope] = json.dumps(packet) + '\n'
    tests.append({'name': 'old_DI_mode_marker_is_ignored', 'expected': True,
                  'data': data})

    # This is a valid raw alias of I(0,S0;u.0)=S0, but coordinate3 under S
    # denotes a dummy zero slot and is not canonical variable syntax.
    alias = json.dumps([[[], 0, [3], 0], [[0, [3], 0], [3]]]) + '\n'
    tests.append({'name': 'dummy_zero_alias_is_not_canonical', 'expected': True,
                  'expected_by_checker': {'strict_checker.py': False},
                  'data': {'local': alias, 'global': alias}})

    # Closed semantic impossibility and malformed input controls independent
    # of the inherited producer and raw constructor conventions.
    for name, data in [('empty_certificate', '[]\n'),
                       ('canonical_contradiction', '[[0,[0]]]\n'),
                       ('unallocated_goal_parameter', '[[-1,0]]\n'),
                       ('invalid_json', '[\n'),
                       ('null_input', 'null\n'),
                       ('mapping_input', '{}\n')]:
        tests.append({'name': name, 'expected': False,
                      'data': {'local': data, 'global': data}})

    results = []
    for test in tests:
        row = {k: v for k, v in test.items() if k != 'data'}
        row['runs'] = []
        for checker in CHECKERS:
            scope = 'global' if checker == 'checker_tokens.py' else 'local'
            for optimized in (False, True):
                accepted, error = check(ROOT / 'code' / checker,
                                        test['data'][scope], optimized)
                expected = test.get('expected_by_checker', {}).get(checker, test['expected'])
                passed = accepted == expected
                run = {'checker': checker, 'optimized': optimized,
                       'expected': expected, 'accepted': accepted, 'passed': passed}
                if not passed:
                    run['stderr_tail'] = error
                row['runs'].append(run)
        results.append(row)

    paths = sorted((ROOT / 'code').glob('*.py'))
    paths += sorted((ROOT / 'reference/checkers').glob('*.py'))
    metrics = {'python': sys.version, 'zlib_version': zlib.ZLIB_VERSION,
               'zlib_runtime_version': zlib.ZLIB_RUNTIME_VERSION,
               'normalization': 'remove true module/function/class docstrings; ast.unparse + newline',
               'gzip': 'level=9, mtime=0; supplemental metric only',
               'programs': [measure(path) for path in paths]}
    validation = {'scope': 'Executable examples, canonical proof-tree audit, and adversarial controls; not proof-assistant verification.',
                  'tests': len(results),
                  'checker_runs': sum(len(r['runs']) for r in results),
                  'passed_runs': sum(run['passed'] for r in results for run in r['runs']),
                  'positive_named_proof_trees': sum(c['expected'] for c in cases),
                  'all_positive_DI_mirrored': all(c['audit']['nonmirrored_atomic_DI'] == 0 for c in cases if c['expected']),
                  'all_positive_D_subformulas_mirrored': all(c['audit']['nonmirrored_atomic_D_subformulas'] == 0 for c in cases if c['expected']),
                  'all_positive_Tr_sources_nonzero': all(c['audit']['zero_source_transport'] == 0 for c in cases if c['expected']),
                  'results': results}
    (evidence / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    (evidence / 'validation.json').write_text(json.dumps(validation, indent=2) + '\n')
    summary = {k: v for k, v in validation.items() if k != 'results'}
    print(json.dumps(summary, indent=2))
    if validation['passed_runs'] != validation['checker_runs']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
