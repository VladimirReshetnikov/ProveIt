"""Independent public-language audit and pinned end-to-end regression checks."""
from pathlib import Path
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

ROOT = Path(__file__).resolve().parent
HERE = ROOT
CONTROL = ROOT / 'controls/native780.py'
PROGRAMS = [CONTROL, HERE / 'fused_native.py', HERE / 'fused_scoped.py']
FIXTURES = ROOT / 'fixtures'


def term(a, slots):
    """Independent interpretation: zero or one of the protected slots."""
    if type(a) is int:
        return a == 0 or a >= 3 and a % 2 == 1 and (a - 3) // 2 < slots
    if type(a) is not list:
        return False
    if len(a) == 1:
        return term(a[0], slots + 2)  # Successor has two dummy slots.
    if len(a) == 3:
        return all(term(t, slots + 1) for t in a)
    return False


def formula(a, slots=0):
    if type(a) is not list:
        return False
    if len(a) == 1:
        return formula(a[0], slots + 2)
    if len(a) == 2:
        return term(a[0], slots) and term(a[1], slots)
    return False


class EnteredKernel(Exception):
    pass


def gate(path):
    """Stop exactly when checking reaches its first certificate packet."""
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.Import, ast.FunctionDef))]
    c = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'c')
    for j, statement in enumerate(c.body):
        if isinstance(statement, ast.Assign) and any(isinstance(t, ast.Tuple) for t in statement.targets):
            c.body[j] = ast.Raise(exc=ast.Call(func=ast.Name(id='EnteredKernel', ctx=ast.Load()), args=[], keywords=[]), cause=None)
            break
    else:
        raise AssertionError('The pinned first-packet marker changed')
    ast.fix_missing_locations(tree)
    namespace = {'EnteredKernel': EnteredKernel}
    exec(compile(tree, str(path), 'exec'), namespace)

    def accept(a):
        try:
            if path == CONTROL:
                if not namespace['v'](a):
                    return False, 'grammar'
                namespace['c'](a)
            else:
                namespace['c'](a, v=1)
        except EnteredKernel:
            return True, 'valid'
        except Exception as error:
            return False, type(error).__name__
        return True, 'early leaf'
    return accept


def sizes(path):
    source = path.read_bytes()
    tree = ast.parse(source)
    normal = (ast.unparse(tree) + '\n').encode()
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}
    return {'path': str(path.relative_to(ROOT)), 'normalized_bytes': len(normal),
            'tokens': sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(normal.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9': len(gzip.compress(normal, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(source).hexdigest()}


def main():
    gates = [gate(p) for p in PROGRAMS]
    failures = []
    exceptions = [dict() for _ in PROGRAMS]
    count = 0

    def check(a):
        nonlocal count
        expected = formula(a)
        for j, g in enumerate(gates):
            accepted, status = g(a)
            exceptions[j][status] = exceptions[j].get(status, 0) + 1
            if accepted != expected or status == 'RecursionError':
                failures.append({'index': count, 'value': a, 'program': str(PROGRAMS[j]), 'expected': expected, 'accepted': accepted, 'status': status})
        count += 1

    atoms = [-3, -1, 0, 1, 2, 3, 4, 5, 7, 9, True, False, None, 0.0, 1.5, '', 'not empty', {}, {'x': 0}]
    for a in atoms:
        check(a)
    for arity in range(5):
        for children in itertools.product(atoms, repeat=arity):
            check(list(children))

    rng = random.Random(20261111)

    def random_term(slots, fuel):
        if fuel <= 0 or rng.random() < .45:
            return rng.choice([0] + [3 + 2*j for j in range(slots)])
        if rng.randrange(2):
            return [random_term(slots + 2, fuel - 1)]
        return [random_term(slots + 1, fuel - 1) for _ in range(3)]

    def random_formula(slots, fuel):
        if fuel > 0 and rng.random() < .4:
            return [random_formula(slots + 2, fuel - 1)]
        return [random_term(slots, fuel), random_term(slots, fuel)]

    for _ in range(3000):
        a = random_formula(0, 4)
        check(a)
        b = copy.deepcopy(a)
        node = b
        while type(node) is list and node and rng.random() < .8:
            index = rng.randrange(len(node))
            if type(node[index]) is list:
                node = node[index]
            else:
                node[index] = rng.choice(atoms)
                break
        else:
            if node:
                node[rng.randrange(len(node))] = rng.choice(atoms)
        check(b)

    cases = next(x['cases'] for x in json.loads((FIXTURES/'cases.json').read_text())['pairs'] if x['name']=='native')
    cli = []
    for case in cases:
        payload = (FIXTURES / case['file'].removeprefix('tests/')).read_bytes()
        for path in PROGRAMS:
            for flags in [[], ['-O']]:
                result = subprocess.run([sys.executable, *flags, str(path)], input=payload, capture_output=True, timeout=10)
                accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
                row = {'fixture': case['file'], 'program': str(path.relative_to(ROOT)), 'optimized': bool(flags), 'expected': case['expected'], 'accepted': accepted}
                cli.append(row)
                if accepted != case['expected']:
                    failures.append(row)
    report = {'python_version': sys.version, 'syntax_cases': count, 'syntax_program_checks': count * len(PROGRAMS),
              'syntax_recursion_errors': sum(x.get('RecursionError', 0) for x in exceptions),
              'syntax_outcomes': exceptions, 'pinned_fixtures': len(cases),
              'cli_checks': len(cli), 'metrics': [sizes(p) for p in PROGRAMS],
              'compact_control_metrics': sizes(ROOT/'controls/compact508.py'),
              'failures': failures, 'cli_results': cli}
    (HERE/'fusion_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'cli_results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
