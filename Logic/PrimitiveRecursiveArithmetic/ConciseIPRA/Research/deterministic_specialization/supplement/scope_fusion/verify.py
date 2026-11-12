"""Check the same complete certificate contract and fused entry invariant."""
import ast
import copy
import gzip
import hashlib
import io
import itertools
import json
import random
import subprocess
import sys
import tokenize
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent


def functions(path):
    tree = ast.parse(path.read_text())
    tree.body = [node for node in tree.body if isinstance(node, ast.FunctionDef)]
    env = {}
    exec(compile(tree, str(path), 'exec'), env)
    return env


class ProofStarted(Exception):
    pass


def start():
    raise ProofStarted


def entry_accepts(env, goal, fused):
    env['q'] = start
    try:
        if fused:
            env['c'](goal, v=1)
        else:
            if not env['v'](goal):
                return False
            env['c'](goal)
    except ProofStarted:
        return True
    except Exception:
        return False
    return True


def invoke(job):
    name, raw, expected, filename, optimized = job
    cmd = [sys.executable] + (['-O'] if optimized else []) + [str(HERE / filename)]
    p = subprocess.run(cmd, input=raw, text=True, capture_output=True, timeout=15)
    accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
    return {'name': name, 'program': filename, 'optimized': optimized,
            'accepted': accepted, 'expected': expected, 'returncode': p.returncode}


def measure(path):
    tree = ast.parse(path.read_text())
    source = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(source.decode()).readline))
    compressed = gzip.compress(source, compresslevel=9, mtime=0)
    path.with_suffix('.normalized.py').write_bytes(source)
    path.with_suffix('.normalized.py.gz').write_bytes(compressed)
    return {'program': path.name, 'normalized_bytes': len(source),
            'significant_tokens': tokens, 'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_bytes': len(compressed),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    old = functions(HERE / 'control.py')
    new = functions(HERE / 'checker.py')
    atoms = [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9]
    goals = list(atoms)
    goals.extend(list(t) for n in range(5) for t in itertools.product(atoms, repeat=n))
    rng = random.Random(20261111)

    def random_tree(depth):
        if depth == 0 or rng.randrange(4) == 0:
            return rng.choice(atoms)
        return [random_tree(depth - 1) for _ in range(rng.randrange(5))]

    goals.extend(random_tree(5) for _ in range(6000))
    scoped = [0, [0], [0, 0, 0]]
    for _ in range(4):
        scoped.extend([[t] for t in scoped[:12]])
        goals.extend([[t, t] for t in scoped])
        goals.extend([[[t, t]] for t in scoped])
        goals.extend([[[t, t]] * 3 for t in scoped])
    for a in goals:
        if entry_accepts(old, copy.deepcopy(a), False) != entry_accepts(new, copy.deepcopy(a), True):
            raise AssertionError(('entry mismatch', a))

    manifest = json.loads((HERE / 'tests' / 'manifest.json').read_text())
    cases = []
    for item in manifest:
        data = (HERE / 'tests' / item['file']).read_bytes()
        # Source fixtures are copied byte-for-byte from pinned GitHub.
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise AssertionError(('fixture changed', item['name']))
        cases.append((item['name'], data.decode(), item['expected']))
    valid = json.loads((HERE / 'tests' / 'native_computation.json').read_text())
    for label, prefix, expected in [('null', None, False), ('bool', True, False),
                                   ('float', 0.0, False), ('str', '', False),
                                   ('object', {}, False), ('integer', 123, True),
                                   ('negative', -99, True), ('empty_list', [], True)]:
        cases.append(('unused_' + label, json.dumps([prefix] + valid), expected))
    for i, raw in enumerate(['', '[', '[] trailing', '[1,]', '[+1]', '[01]', '{',
                             'null', 'true', '0.0', 'NaN', 'Infinity', '{}', '"[]"', '[]']):
        cases.append(('bad_json_' + str(i), raw, False))
    for i, goal in enumerate([0, [], [3, 3], [999, 999], [[5, 5]] * 3,
                             [[7, 7]], [[7], [7]], [[5, 0, 0], 0],
                             [[0, 5, 0], 0], [[0, 0, 5], 0],
                             [-1, -1], [4, 4], [1, 1], [2, 2],
                             [[0, 0], [0, [0]], [0, 0]]]):
        cases.append(('bad_goal_' + str(i), json.dumps([[0, 0, [0], 0], goal]), False))
    jobs = [(name, raw, expected, filename, opt) for name, raw, expected in cases
            for filename in ['control.py', 'checker.py'] for opt in [False, True]]
    with ThreadPoolExecutor(max_workers=8) as pool:
        records = list(pool.map(invoke, jobs))
    for row in records:
        if row['accepted'] != row['expected']:
            raise AssertionError(('unexpected CLI result', row))
    result = {'status': 'passed', 'python': sys.version,
              'entry_shapes_compared': len(goals), 'fixture_count': len(manifest),
              'cli_cases': len(cases), 'cli_runs': len(records),
              'metrics': [measure(HERE / 'control.py'), measure(HERE / 'checker.py')],
              'records': records,
              'limitation': 'Finite tests supplement the entry-invariant proof; no proof-assistant verification.'}
    (HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    main()
