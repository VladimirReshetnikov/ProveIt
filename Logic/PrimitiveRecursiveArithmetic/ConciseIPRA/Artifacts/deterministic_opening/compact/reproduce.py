"""Reproduce continuation-fusion metrics, provenance, and finite checks.

The written trace proof, not these finite tests, proves program equivalence.
Run with Python 3.12.14 for the recorded normalization metrics.
"""
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

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENDMARKER, tokenize.ENCODING, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PAIRS = [(name, ROOT / 'baseline' / (name + '.py'),
          ROOT / 'code' / (name + '.py'))
         for name in ('compact', 'ast', 'native')]


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'file': path.relative_to(ROOT).as_posix(),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in SKIP for t in
                                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'git_blob_sha1': git_blob(raw),
    }


def run(path, payload, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(path)], input=payload,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=30)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def functions(path):
    # This extraction is only a test harness. The standalone CLI is tested above.
    tree = ast.parse(path.read_text())
    tree.body = [node for node in tree.body if isinstance(
        node, (ast.Import, ast.ImportFrom, ast.FunctionDef))]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


def check(namespace, payload):
    data = copy.deepcopy(payload)
    try:
        goal = data.pop()
        namespace['q'] = data.pop
        if 'v' in namespace and not namespace['v'](goal):
            return False, None
        namespace['c'](goal)
        return True, len(data)
    except Exception:
        return False, None


def main():
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    for record in provenance['authenticated_files']:
        data = (ROOT / record['local_path']).read_bytes()
        if git_blob(data) != record['git_blob_sha1']:
            raise ValueError('Changed authenticated source: ' + record['local_path'])
    metrics = []
    for name, control, candidate in PAIRS:
        for role, path in [('control', control), ('candidate', candidate)]:
            metrics.append({'pair': name, 'role': role, **measure(path)})
    metrics.append({'pair': 'token_frontier', 'role': 'control',
                    **measure(ROOT / 'baseline' / 'tokens.py')})
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(
        {'python': sys.version, 'programs': metrics}, indent=2) + '\n')

    cases = json.loads((ROOT / 'fixtures' / 'cases.json').read_text())
    checks = []
    for name, control, candidate in PAIRS:
        for optimized in (False, True):
            for case in cases:
                payload = (ROOT / 'fixtures' / case['file']).read_bytes()
                a, b = run(control, payload, optimized), run(candidate, payload, optimized)
                # The native and guarded interfaces intentionally classify two
                # auxiliary fixtures differently. Compare each matched pair.
                checks.append({'pair': name, 'case': case['name'],
                               'optimized': optimized, 'control': a,
                               'candidate': b, 'same': a == b})
                if name != 'native' and a != case['expected']:
                    raise AssertionError(('Control outcome', name, case['name'], a))

    namespaces = {name: (functions(a), functions(b)) for name, a, b in PAIRS}
    rng = random.Random(17898)
    pool = [0, 1, -1, -2, -100, 3, 5, [], [0], [1], [0, 0], [0, [0]],
            [0, 0, 0], [[0, 0]], [[[0, 0, 0], [0, 0, 0]]]]
    for j in range(500):
        case = rng.choice(cases)
        payload = json.loads((ROOT / 'fixtures' / case['file']).read_text())
        if len(payload) > 1:
            index = rng.randrange(len(payload) - 1)
            if rng.randrange(4) == 0:
                payload[index] = copy.deepcopy(rng.choice(pool))
            elif isinstance(payload[index], list) and payload[index]:
                payload[index][rng.randrange(len(payload[index]))] = copy.deepcopy(rng.choice(pool))
        if rng.randrange(5) == 0:
            payload.insert(0, copy.deepcopy(rng.choice(pool)))
        for name, (a, b) in namespaces.items():
            left, right = check(a, payload), check(b, payload)
            checks.append({'pair': name, 'mutation': j, 'control': left,
                           'candidate': right, 'same': left == right})

    fresh = [[0, 0, [-1], 0], [0, 0, 0, 0], [[[0, 5, 0], 3]]]
    for name, (a, b) in namespaces.items():
        left, right = check(a, fresh), check(b, fresh)
        checks.append({'pair': name, 'case': 'used_fresh_parameter',
                       'control': left, 'candidate': right, 'same': left == right})
        if left != (True, 0):
            raise AssertionError(('Fresh-parameter control', name, left))
    report = {
        'scope': 'Finite regression tests; universal equivalence has a separate written proof.',
        'seed': 17898, 'cli_paired_comparisons': 126, 'cli_executions': 252,
        'mutation_cases': 500, 'mutation_pair_checks': 1500,
        'fresh_parameter_pair_checks': 3,
        'all_equal': all(item['same'] for item in checks), 'checks': checks,
    }
    (ROOT / 'evidence' / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    if not report['all_equal']:
        raise AssertionError([item for item in checks if not item['same']])
    print(json.dumps({key: value for key, value in report.items() if key != 'checks'}, indent=2))


if __name__ == '__main__':
    main()
