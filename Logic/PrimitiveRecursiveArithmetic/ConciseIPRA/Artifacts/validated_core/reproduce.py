#!/usr/bin/env python3
"""Recompute whole-module metrics and the frozen verification suite offline."""
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
import random
import subprocess
import sys
import tempfile
import tokenize
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
EVIDENCE.mkdir(exist_ok=True)
IGNORE = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
          tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def measure(path):
    original = path.read_bytes()
    normalized = (ast.unparse(ast.parse(original.decode('utf-8'))) + '\n').encode()
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    destination = EVIDENCE / 'gzip' / path.parent.name / (path.name + '.gz')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(compressed)
    return {'file': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in IGNORE for t in tokens),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'normalized_bytes': len(normalized), 'gzip9_bytes': len(compressed),
            'source_sha256': digest(original), 'normalized_sha256': digest(normalized)}


programs = [measure(p) for group in ('code', 'reference')
            for p in sorted((ROOT / group).glob('*.py'))]
metrics = {'python': platform.python_version(),
           'normalization': 'CPython ast.unparse(ast.parse(source)) plus one LF; entire module, no docstring removal',
           'gzip': 'gzip.compress(level=9, mtime=0), wrapper included; informational only',
           'programs': programs}
(EVIDENCE / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
with (EVIDENCE / 'metrics.csv').open('w', newline='') as f:
    writer = csv.DictWriter(f, fieldnames=list(programs[0]))
    writer.writeheader()
    writer.writerows(programs)

manifest = json.loads((ROOT / 'tests/manifest.json').read_text())
jobs = []
for row in manifest:
    for optimized in (False, True):
        for group in ('code', 'reference'):
            jobs.append((row, optimized, group, row['profile']))
        if row['profile'] == 'native_typed_full.py':
            jobs.append((row, optimized, 'code', 'readable_native.py'))


def execute(job):
    row, optimized, group, program = job
    fixture = row['input'] if group == 'code' else row['reference_input']
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / group / program)]
    try:
        run = subprocess.run(command, input=(ROOT / fixture).read_bytes(),
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             timeout=30)
        accepted = run.returncode == 0 and run.stdout == b'ACCEPT\n'
        return {'case': row['name'], 'program': group + '/' + program,
                'optimized': optimized, 'expected': row['expected'],
                'accepted': accepted, 'returncode': run.returncode,
                'error_tail': run.stderr.decode(errors='replace')[-180:] if accepted != row['expected'] else ''}
    except subprocess.TimeoutExpired:
        return {'case': row['name'], 'program': group + '/' + program,
                'optimized': optimized, 'expected': row['expected'],
                'accepted': False, 'error': 'timeout'}


with ThreadPoolExecutor(max_workers=4) as pool:
    receipts = list(pool.map(execute, jobs))
failures = [r for r in receipts if 'error' in r or r['accepted'] != r['expected']]

# Finite differential checks accompany the universal structural argument.
# Load only v and j definitions; never execute a checker's stdin/main program.
def validators(path):
    tree = ast.parse(path.read_text())
    ns = {}
    nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in ('v', 'j')]
    exec(compile(ast.Module(nodes, []), str(path), 'exec'), ns)
    if 'j' in ns:
        return ns['v'], ns['j']
    raw = ns['v']
    return (lambda value, depth=0: raw(value, depth + 2)), raw


def verdict(predicate, value, *args):
    try:
        return bool(predicate(value, *args))
    except (TypeError, IndexError, RecursionError):
        return False


rng = random.Random(11112026)
leaves = [0, 1, 2, 3, 4, 5, -1, -5, True, False, 0.0, 1.5, None, '', 'a', {}, {'x': 1}]

def random_tree(depth):
    if depth == 0 or rng.randrange(3) == 0:
        return rng.choice(leaves)
    return [random_tree(depth - 1) for _ in range(rng.randrange(5))]


def numerical(depth, slots=0):
    if depth == 0:
        return rng.choice([0] + list(range(3, 3 + 2 * slots, 2)))
    n = rng.randrange(3)
    if n == 0:
        return numerical(0, slots)
    if n == 1:
        return [numerical(depth - 1, slots + 2)]
    return [numerical(depth - 1, slots + 1) for _ in range(3)]


def formula(depth, slots=0):
    if depth == 0 or rng.randrange(3) == 0:
        return [numerical(2, slots), numerical(2, slots)]
    body = formula(depth - 1, slots + (2 if rng.randrange(2) else 1))
    # This deliberate independent wrapper choice also makes near-valid controls.
    return [body] if rng.randrange(2) else [body, body, body]


samples = leaves + [random_tree(4) for _ in range(1600)] + [formula(4) for _ in range(300)]
validator_receipts = []
for name in ('native_typed_full.py', 'native_typed_eqd.py'):
    old_v, old_j = validators(ROOT / 'reference' / name)
    new_v, new_j = validators(ROOT / 'code' / name)
    counts = {'samples': len(samples), 'typed': 0, 'goal_checks': 0, 'differences': []}
    for index, value in enumerate(samples):
        left, right = verdict(old_j, value), verdict(new_j, value)
        if left != right:
            counts['differences'].append({'sample': index, 'part': 'whole-tree type'})
        if not left:
            continue
        counts['typed'] += 1
        for depth in range(0, 10):
            counts['goal_checks'] += 1
            if verdict(old_v, value, depth) != verdict(new_v, value, depth):
                counts['differences'].append({'sample': index, 'depth': depth, 'part': 'canonical grammar'})
    counts['profile'] = name
    validator_receipts.append(counts)
    failures.extend(counts['differences'])

# A concrete negative result: the opener's parity safeguard cannot be deleted.
mutation = {'control_rejects_false_goal': True, 'mutant_accepts_false_goal': []}
with tempfile.TemporaryDirectory() as temporary:
    source = (ROOT / 'reference/guarded_bytes.py').read_text()
    mutant_source = source.replace('else d % 2 and i(t, d=3)', 'else i(t, d=3)')
    if mutant_source == source:
        failures.append({'mutation': 'parity substitution did not match'})
    mutant = Path(temporary) / 'unsafe_no_parity.py'
    mutant.write_text(mutant_source)
    raw = (ROOT / 'tests/parity_guard_original.json').read_bytes()
    for optimized in (False, True):
        run = subprocess.run([sys.executable] + (['-O'] if optimized else []) + [str(mutant)],
                             input=raw, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        accepted = run.returncode == 0 and run.stdout == b'ACCEPT\n'
        mutation['mutant_accepts_false_goal'].append({'optimized': optimized, 'accepted': accepted})
        if not accepted:
            failures.append({'mutation': 'the advertised parity counterexample did not reproduce'})

summary = {'python': platform.python_version(), 'status': 'PASS' if not failures else 'FAIL',
           'scope': 'Finite process and validator checks; universal correctness is proved in the accompanying argument, not by these tests',
           'process_executions': len(receipts),
           'expected_acceptances': sum(r['expected'] for r in receipts),
           'expected_rejections': sum(not r['expected'] for r in receipts),
           'validator_checks': validator_receipts, 'parity_counterexample': mutation,
           'failures': failures, 'receipts': receipts}
(EVIDENCE / 'validation.json').write_text(json.dumps(summary, indent=2) + '\n')
lines = []
for path in sorted(ROOT.rglob('*')):
    if not path.is_file() or '__pycache__' in path.parts or path.name == 'SHA256SUMS':
        continue
    lines.append(digest(path.read_bytes()) + '  ' + str(path.relative_to(ROOT)))
(ROOT / 'SHA256SUMS').write_text('\n'.join(lines) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'receipts'}, indent=2))
if failures:
    raise SystemExit(1)
