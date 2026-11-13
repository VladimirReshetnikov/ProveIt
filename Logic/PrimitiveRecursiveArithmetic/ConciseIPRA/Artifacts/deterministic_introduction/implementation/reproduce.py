"""Reproduce the separate implementation refinement; Python stdlib only."""
from pathlib import Path
import ast
import copy
import gzip
import hashlib
import io
import json
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PAIRS = [(ROOT/'controls/native780.py', ROOT/'code/native.py', 'native'),
         (ROOT/'controls/compact508.py', ROOT/'code/compact_optional.py', 'compact')]
SKIP = {tokenize.ENDMARKER, tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def functions(path):
    tree = ast.parse(path.read_text())
    tree.body = [x for x in tree.body if isinstance(x, (ast.Import, ast.ImportFrom, ast.FunctionDef))]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace

class FirstPacket(Exception):
    pass

def stop():
    raise FirstPacket

def first_scan(namespace, goal, selected):
    namespace['q'] = stop
    try:
        if not selected and not namespace['v'](goal):
            return False
        namespace['c'](goal, v=1) if selected else namespace['c'](goal)
        return True
    except FirstPacket:
        return True
    except BaseException:
        return False

def trace(namespace, payload, kind, selected):
    data = copy.deepcopy(payload)
    try:
        goal = data.pop()
        namespace['q'] = data.pop
        if kind == 'native':
            if selected:
                namespace['c'](goal, v=1)
            elif namespace['v'](goal):
                namespace['c'](goal)
            else:
                return False, None
        else:
            namespace['c'](goal)
        return True, len(data)
    except BaseException:
        return False, None

provenance = json.loads((ROOT/'PROVENANCE.json').read_text())
for item in provenance['controls']:
    if hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest() != item['sha256']:
        raise AssertionError(('Changed frozen control', item['path']))

old, new = functions(PAIRS[0][0]), functions(PAIRS[0][1])
rng = random.Random(665330)
leaves = [None, False, True, 0, 1, 2, 3, 4, 5, 6, 7, -1, -2, -3,
          0.0, 1.0, 3.0, 1.5, -0.5, '', 'x', '0', {}, {'a': 0}, [], [0],
          [3], [0, 0], [0, [0]], [0, 0, 0]]
def random_tree(depth):
    if depth <= 0 or rng.randrange(3) == 0:
        return copy.deepcopy(rng.choice(leaves))
    return [random_tree(depth - 1) for _ in range(rng.randrange(6))]

goals = leaves + [random_tree(5) for _ in range(20000)]
for goal in goals:
    left, right = first_scan(old, goal, False), first_scan(new, goal, True)
    if left != right:
        raise AssertionError(('first scan', goal, left, right))

def term(depth, fuel):
    if fuel <= 0 or rng.randrange(3) == 0:
        return rng.choice([0] + list(range(3, max(4, depth + 4), 2)))
    if rng.randrange(2):
        return [term(depth + 4, fuel - 1)]
    return [term(depth + 2, fuel - 1) for _ in range(3)]
def formula(depth, fuel):
    if fuel <= 0 or rng.randrange(2):
        return [term(depth + 3, 3), term(depth + 3, 3)]
    return [formula(depth + 4, fuel - 1)]
for _ in range(10000):
    goal = formula(0, 4)
    left, right = first_scan(old, goal, False), first_scan(new, goal, True)
    if left != right:
        raise AssertionError(('grammar scan', goal, left, right))

cases = json.loads((ROOT/'fixtures/cases.json').read_text())
checks, trace_checks, metrics = [], [], []
for control, candidate, kind in PAIRS:
    namespaces = functions(control), functions(candidate)
    for case in cases:
        payload = json.loads((ROOT/'fixtures'/case['file']).read_text())
        outcomes = [trace(ns, payload, kind, selected) for ns, selected in zip(namespaces, (False, True))]
        if outcomes[0] != outcomes[1]:
            raise AssertionError(('trace', kind, case, outcomes))
        trace_checks.append({'pair': kind, 'case': case['name'], 'outcome': outcomes[0]})
    for optimized in (False, True):
        for case in cases:
            payload = (ROOT/'fixtures'/case['file']).read_bytes()
            results = []
            for path in (control, candidate):
                result = subprocess.run([sys.executable, '-I', '-S', '-B'] +
                                        (['-O'] if optimized else []) + [str(path)],
                                        input=payload, capture_output=True, timeout=30)
                results.append({'accepted': result.returncode == 0 and result.stdout == b'ACCEPT\n',
                                'exit': result.returncode, 'stdout': result.stdout.decode()})
            if results[0]['accepted'] != results[1]['accepted']:
                raise AssertionError(('CLI', kind, case, optimized, results))
            checks.append({'pair': kind, 'case': case['name'], 'optimized': optimized,
                           'control': results[0], 'selected': results[1]})
    for path in (control, candidate):
        tree = ast.parse(path.read_text())
        normalized = ast.unparse(tree) + '\n'
        metrics.append({'file': path.relative_to(ROOT).as_posix(),
                        'bytes': len(normalized.encode()),
                        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
                        'ast_nodes': sum(1 for _ in ast.walk(tree)),
                        'gzip9': len(gzip.compress(normalized.encode(), mtime=0)),
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
report = {'python': sys.version, 'all_passed': True,
          'random_json_initial_scans': len(goals), 'generated_grammar_scope_scans': 10000,
          'trace_pairs': len(trace_checks), 'cli_pairs': len(checks), 'cli_processes': 2*len(checks),
          'metrics': metrics, 'trace_checks': trace_checks, 'cli_checks': checks}
(ROOT/'verification.json').write_text(json.dumps(report, indent=2) + '\n')
(ROOT/'metrics.json').write_text(json.dumps({'python': sys.version, 'programs': metrics}, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ('trace_checks', 'cli_checks')}, indent=2))
