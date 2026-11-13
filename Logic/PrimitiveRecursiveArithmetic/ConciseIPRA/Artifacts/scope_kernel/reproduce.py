"""Check the two matched scope-reuse profiles, with targeted JSON controls."""
import ast
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import io
import json
import platform
import random
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
INCOMING = ROOT / 'reference/validated_core'
PROFILES = {
    'full': ('native_typed_full.py', 'code/checker_full.py'),
    'eqd': ('native_typed_eqd.py', 'code/checker_eqd.py'),
}


def namespace(path):
    tree = ast.parse(path.read_text())
    ns = {}
    body = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    exec(compile(ast.Module(body, []), str(path), 'exec'), ns)
    return ns


class ProofBoundary(Exception):
    pass


def reached_proof():
    raise ProofBoundary


def validator(ns, a):
    try:
        return bool(ns['v'](a, 2))
    except (TypeError, IndexError, RecursionError):
        return False


def preflight(ns, a):
    try:
        if not ns['v'](a, 2):
            return False
        ns['c'](a)
        return True
    except ProofBoundary:
        return True
    except (TypeError, IndexError, RecursionError):
        return False


rng = random.Random(862881)
leaves = [0, -1, 1, 2, 3, 4, 5, 7, 15, 31, True, False, 0.0, 1.5,
          None, '', 'a', {}, {'x': 1}]


def raw(depth):
    if not depth or rng.randrange(3) == 0:
        return rng.choice(leaves)
    return [raw(depth - 1) for _ in range(rng.randrange(5))]


def term(depth, scope=3, valid=False):
    if not depth or rng.randrange(3) == 0:
        return rng.choice([0] + (list(range(3, scope, 2)) if valid else
                                 list(range(-1, 24))))
    arity = rng.choice([1, 3])
    return [term(depth - 1, scope + 5 - arity, valid) for _ in range(arity)]


def formula(depth, scope=0, valid=False, full=True):
    if not depth or rng.randrange(3) == 0:
        return [term(3, scope + 3, valid) for _ in range(2)]
    arity = rng.choice([1, 3]) if full else 1
    body = formula(depth - 1, scope + 5 - arity, valid, full)
    return [body] * arity


samples = leaves + [raw(4) for _ in range(4000)]
samples += [formula(4) for _ in range(6000)]
samples += [formula(4, valid=True) for _ in range(1500)]
samples += [formula(4, valid=True, full=False) for _ in range(1500)]
scope_receipts = []
for label, (old_name, new_name) in PROFILES.items():
    old = namespace(INCOMING / 'code' / old_name)
    new = namespace(ROOT / new_name)
    new['q'] = reached_proof
    differences = []
    valid_count = 0
    for n, a in enumerate(samples):
        left, right = validator(old, a), preflight(new, a)
        valid_count += left
        if left != right:
            differences.append({'index': n, 'value': a, 'old': left, 'new': right})
    scope_receipts.append({'profile': label, 'samples': len(samples),
                           'valid_goals': valid_count, 'differences': differences})

good = json.loads((INCOMING / 'tests/native_computation.json').read_text())
extra = []
for name, value in [('null', None), ('false', False), ('true', True),
                    ('zero_float', 0.0), ('positive_float', 1.5),
                    ('empty_string', ''), ('nonempty_string', '[]'),
                    ('empty_object', {}), ('nonempty_object', {'0': 0}),
                    ('number', 1), ('empty_array', [])]:
    extra.append({'name': 'root_' + name, 'input': value, 'expected': False})
for name, value in [('null', None), ('false', False), ('float', 0.0),
                    ('string', 'x'), ('object', {'x': 0})]:
    extra.append({'name': 'unused_prefix_' + name,
                  'input': [value] + good, 'expected': False})
for name, value in [('integer', 123), ('negative_integer', -99), ('list', [])]:
    extra.append({'name': 'unused_prefix_' + name,
                  'input': [value] + good, 'expected': True})
for name, goal in [('high_slot', [999, 999]),
                   ('negative_escape', [-1, -1]),
                   ('even_slot', [4, 4]),
                   ('small_slot', [1, 1]),
                   ('nested_high_slot', [[999], [999]]),
                   ('D_high_slot', [[999, 999]]),
                   ('Q_high_slot', [[999, 999]] * 3),
                   ('bool_equation', [False, False]),
                   ('float_equation', [0.0, 0.0]),
                   ('null_equation', [None, None]),
                   ('canonical_false', [0, [0]])]:
    extra.append({'name': name, 'input': good[:-1] + [goal], 'expected': False})
(ROOT / 'evidence/adversarial_cases.json').write_text(json.dumps(extra, indent=2) + '\n')

manifest = json.loads((INCOMING / 'tests/manifest.json').read_text())
jobs = []
for label, (old_name, new_name) in PROFILES.items():
    programs = [INCOMING / 'code' / old_name, ROOT / new_name]
    if label == 'full':
        programs.append(ROOT / 'code/checker_readable.py')
    selected = [row for row in manifest if row['profile'] == old_name]
    cases = [{'name': row['name'], 'data': (INCOMING / row['input']).read_bytes(),
              'expected': row['expected']} for row in selected]
    cases += [{'name': row['name'], 'data': json.dumps(row['input']).encode(),
               'expected': row['expected']} for row in extra]
    for row in cases:
        for program in programs:
            for optimized in [False, True]:
                jobs.append((label, row, program, optimized))


def execute(job):
    label, row, program, optimized = job
    r = subprocess.run([sys.executable] + (['-O'] if optimized else []) + [str(program)],
                       input=row['data'], capture_output=True, timeout=10)
    accepts = r.returncode == 0 and r.stdout == b'ACCEPT\n'
    return {'profile': label, 'case': row['name'], 'program': program.name,
            'optimized': optimized, 'expected': row['expected'], 'accepted': accepts}


with ThreadPoolExecutor(max_workers=4) as pool:
    receipts = list(pool.map(execute, jobs))
failures = [r for r in receipts if r['accepted'] != r['expected']]

metrics = []
for name in ['reference/validated_core/code/native_typed_full.py', 'code/checker_full.py', 'reference/validated_core/code/native_typed_eqd.py', 'code/checker_eqd.py',
             'code/checker_readable.py']:
    path = ROOT / name
    data = path.read_bytes()
    normalized = (ast.unparse(ast.parse(data.decode())) + '\n').encode()
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    (ROOT / 'evidence' / (Path(name).name + '.normalized.gz')).write_bytes(compressed)
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    ignored = {tokenize.COMMENT, tokenize.ENCODING, tokenize.ENDMARKER,
               tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL}
    metrics.append({'file': name, 'normalized_bytes': len(normalized),
                    'tokens': sum(t.type not in ignored for t in tokens),
                    'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
                    'gzip9_bytes': len(compressed),
                    'source_sha256': hashlib.sha256(data).hexdigest()})
(ROOT / 'evidence/metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
summary = {'python': platform.python_version(), 'scope_checks': scope_receipts,
           'extra_case_count': len(extra), 'process_executions': len(receipts),
           'process_failures': failures, 'processes': receipts}
(ROOT / 'evidence/validation.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'processes'}, indent=2))
print(json.dumps(metrics, indent=2))
if failures or any(r['differences'] for r in scope_receipts):
    raise SystemExit(1)
