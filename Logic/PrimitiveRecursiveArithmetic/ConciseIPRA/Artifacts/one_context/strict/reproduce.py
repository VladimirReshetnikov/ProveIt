"""Reproduce matched checker measurements and scope-factorization checks."""
from pathlib import Path
import ast
import concurrent.futures
import gzip
import hashlib
import io
import itertools
import json
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PAIRS = [
    ('control_shared_strict_eqd.py', 'checker_eqd.py', 'eqd'),
    ('control_shared_strict_full.py', 'checker_full.py', 'full'),
    ('control_shared_typed.py', 'checker_typed.py', 'full'),
    ('checker_rev_strict_eqd.py', 'checker_rev_eqd.py', 'eqd'),
    ('checker_rev_strict_full.py', 'checker_rev_full.py', 'full'),
    ('checker_rev_typed.py', 'checker_rev_typed.py', 'full'),
]
EXCLUDED = {getattr(tokenize, name) for name in
            ('ENCODING', 'COMMENT', 'NL', 'NEWLINE', 'INDENT', 'DEDENT', 'ENDMARKER')}


def metrics(path):
    source = path.read_bytes()
    tree = ast.parse(source)
    normal = (ast.unparse(tree) + '\n').encode()
    compressed = gzip.compress(normal, compresslevel=9, mtime=0)
    path.with_suffix('.py.gz').write_bytes(compressed)
    return {'path': str(path.relative_to(ROOT)), 'normalized_bytes': len(normal),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'significant_tokens': sum(t.type not in EXCLUDED for t in
                                      tokenize.tokenize(io.BytesIO(normal).readline)),
            'gzip9_bytes': len(compressed), 'raw_bytes': len(source),
            'source_sha256': hashlib.sha256(source).hexdigest(),
            'normalized_sha256': hashlib.sha256(normal).hexdigest()}


def load_validator(path):
    tree = ast.parse(path.read_text())
    node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'v')
    ns = {}
    exec(compile(ast.Module(body=[node], type_ignores=[]), str(path), 'exec'), ns)
    return ns['v']


def load_actual_opener(path):
    tree = ast.parse(path.read_text())
    c = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'c')
    assignment = c.body[0]
    if not (isinstance(assignment, ast.Assign) and isinstance(assignment.value, ast.Lambda)):
        raise ValueError('Expected the unchanged opener as first checker statement')
    def sentinel():
        pass
    ns = {'c': sentinel, 'k': 0}
    exec(compile(ast.Module(body=[assignment], type_ignores=[]), str(path), 'exec'), ns)
    return ns['i']


def passed_opening(opener, a):
    try:
        return opener(a) == a
    except (TypeError, ValueError, RecursionError):
        return False


def parser_checks():
    # This is evidence for the structural theorem, not its replacement.
    atoms = [None, False, True, 0.0, 1.0, '', {}, -3, -1, 0, 1, 2, 3, 4, 5, 7, 9]
    goals = list(atoms)
    goals += [[]]
    for arity in range(1, 4):
        goals.extend(list(t) for t in itertools.product(atoms, repeat=arity))
    for depth in range(8):
        for label in range(-4, 30):
            a = [label, 0]
            for _ in range(depth):
                a = [a]
            goals.append(a)
            goals.append([a, a, a])
    rng = random.Random(20261111)
    def random_tree(depth):
        if depth == 0 or rng.randrange(4) == 0:
            return rng.choice(atoms)
        return [random_tree(depth - 1) for _ in range(rng.randrange(5))]
    goals.extend(random_tree(4) for _ in range(10000))
    rows = []
    for old_name, new_name, grammar in PAIRS[:2]:
        old_path = ROOT / 'reference' / old_name
        old = load_validator(old_path)
        new = load_validator(ROOT / 'code' / new_name)
        opener = load_actual_opener(old_path)
        failures = []
        admitted = 0
        for a in goals:
            x = bool(old(a))
            y = bool(new(a)) and passed_opening(opener, a)
            admitted += x
            if x != y:
                failures.append(a)
        rows.append({'grammar': grammar, 'comparisons': len(goals),
                     'old_admitted': admitted, 'mismatches': len(failures),
                     'first_failures': failures[:5]})
    return rows


def run_task(task):
    checker, certificate, optimize = task
    cmd = [sys.executable] + (['-O'] if optimize else []) + [str(checker)]
    result = subprocess.run(cmd, input=certificate.read_bytes(), capture_output=True,
                            timeout=15)
    return (str(checker.relative_to(ROOT)), str(certificate.relative_to(ROOT)), optimize,
            result.returncode == 0 and result.stdout == b'ACCEPT\n')


def main():
    checks = []
    for old_name, new_name, _ in PAIRS:
        checks.extend([ROOT / 'reference' / old_name, ROOT / 'code' / new_name])
    measurements = [metrics(p) for p in checks]
    files = sorted((ROOT / 'tests/zero_neutral').glob('*.json'))
    files += sorted((ROOT / 'tests/neutral_baseline').glob('*.json'))
    tasks = list(itertools.product(checks, files, [False, True]))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        executions = list(pool.map(run_task, tasks))
    results = {(checker, certificate, optimized): accept
               for checker, certificate, optimized, accept in executions}
    comparisons = []
    for old_name, new_name, grammar in PAIRS:
        for certificate in files:
            for optimized in [False, True]:
                suffix = (str(certificate.relative_to(ROOT)), optimized)
                old = results[(str(Path('reference') / old_name), *suffix)]
                new = results[(str(Path('code') / new_name), *suffix)]
                comparisons.append({'old': old_name, 'new': new_name, 'grammar': grammar,
                                    'certificate': suffix[0], 'optimized': optimized,
                                    'old_accept': old, 'new_accept': new})
    # The proof kernel and all drivers are unchanged; only v differs.
    kernel_identity = []
    for old_name, new_name, _ in PAIRS:
        old_tree = ast.parse((ROOT/'reference'/old_name).read_text())
        new_tree = ast.parse((ROOT/'code'/new_name).read_text())
        def without_v(tree):
            tree.body = [n for n in tree.body if not
                         (isinstance(n, ast.FunctionDef) and n.name == 'v')]
            return ast.dump(tree, include_attributes=False)
        kernel_identity.append({'old': old_name, 'new': new_name,
                                'identical_except_validator': without_v(old_tree) == without_v(new_tree)})
    parser = parser_checks()
    failures = [r for r in comparisons if r['old_accept'] != r['new_accept']]
    receipt = {'python': sys.version, 'process_executions': len(executions),
               'paired_comparisons': len(comparisons), 'mismatches': len(failures),
               'baseline_acceptances': sum(r['old_accept'] for r in comparisons),
               'baseline_rejections': sum(not r['old_accept'] for r in comparisons),
               'kernel_identity': kernel_identity, 'parser_factorization': parser,
               'comparisons': comparisons}
    (ROOT/'metrics.json').write_text(json.dumps(measurements, indent=2) + '\n')
    (ROOT/'validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if failures or any(not x['identical_except_validator'] for x in kernel_identity) or any(x['mismatches'] for x in parser):
        raise SystemExit('FAILED')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'comparisons'}, indent=2))


if __name__ == '__main__':
    main()
