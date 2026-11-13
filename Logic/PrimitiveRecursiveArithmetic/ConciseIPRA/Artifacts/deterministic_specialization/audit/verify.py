"""Independent boundary checks for deterministic Use and redundant scope."""
import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
import random
import subprocess
import sys
import tokenize
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def accepted(module, certificate):
    try:
        module.verify(certificate)
        return True
    except Exception:
        return False


def evaluate(term, bindings=()):
    if type(term) is int:
        if term == 0:
            return 0
        if term < 0:
            raise ValueError('Open evaluation')
        return bindings[term - 1]
    if term[0] == 's':
        return evaluate(term[1], bindings) + 1
    n = evaluate(term[1], bindings)
    value = evaluate(term[2], bindings)
    if n > 10000:
        raise ValueError('Evaluation bound exceeded')
    for _ in range(n):
        value = evaluate(term[3], (value,) + bindings)
    return value


def invoke(job):
    name, raw, expected, filename, optimized = job
    cmd = [sys.executable] + (['-O'] if optimized else []) + [str(HERE / filename)]
    p = subprocess.run(cmd, input=raw, text=True, capture_output=True, timeout=20)
    return {'case': name, 'program': filename, 'optimized': optimized,
            'accepted': p.returncode == 0 and p.stdout == 'ACCEPT\n',
            'expected': expected, 'returncode': p.returncode}


def measure(name):
    path = HERE / (name + '.py')
    tree = ast.parse(path.read_text())
    if ast.get_docstring(tree) is not None:
        tree.body.pop(0)
    data = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(data.decode()).readline))
    compressed = gzip.compress(data, compresslevel=9, mtime=0)
    (HERE / (name + '.normalized.py')).write_bytes(data)
    (HERE / (name + '.normalized.py.gz')).write_bytes(compressed)
    return {'program': name, 'bytes': len(data), 'tokens': tokens,
            'ast': len(list(ast.walk(tree))), 'gzip9': len(compressed),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    names = ['deterministic_explicit', 'deterministic_implicit',
             'unrestricted_explicit', 'unrestricted_implicit']
    modules = {name: load(name) for name in names}
    manifest = json.loads((HERE / 'fixtures/manifest.json').read_text())
    jobs = []
    calls = 0
    scope_violations = []
    checked_equations = 0

    codes = {modules[name].derive.__code__ for name in names if name.endswith('explicit')}

    def check_scope(frame, event, arg):
        nonlocal calls
        if event == 'call' and frame.f_code in codes:
            calls += 1
            if frame.f_locals['scope'] != len(frame.f_locals['context']):
                scope_violations.append((frame.f_locals['scope'], len(frame.f_locals['context'])))

    sys.setprofile(check_scope)
    try:
        for item in manifest:
            raw = (HERE / 'fixtures' / item['file']).read_text()
            cert = json.loads(raw)
            for suffix in ['explicit', 'implicit']:
                name = item['family'] + '_' + suffix
                if accepted(modules[name], cert) != item['expected']:
                    raise AssertionError(('Unexpected import result', item['name'], name))
                for optimized in [False, True]:
                    jobs.append((item['name'], raw, item['expected'], name + '.py', optimized))
            if item['expected'] and cert['goal'][0] == '=':
                if evaluate(cert['goal'][1]) != evaluate(cert['goal'][2]):
                    raise AssertionError(('False closed equation', item['name']))
                checked_equations += 1
    finally:
        sys.setprofile(None)

    if scope_violations:
        raise AssertionError(('Scope invariant violated', scope_violations))

    malformed = ['', '[', '[] trailing', '[1,]', '[+1]', '[01]', '{',
                 'null', 'true', '0.0', 'NaN', 'Infinity', '{}', '"[]"', '[]']
    for i, raw in enumerate(malformed):
        for name in names:
            for optimized in [False, True]:
                jobs.append(('malformed_json_' + str(i), raw, False, name + '.py', optimized))

    deterministic = [json.loads((HERE / 'fixtures' / item['file']).read_text())
                     for item in manifest if item['family'] == 'deterministic' and item['expected']]
    rng = random.Random(112026)
    mutations = 0
    accepted_mutations = 0
    leaves = [None, False, True, 0.0, {}, [], '', -100, -2, -1, 0, 1, 2,
              ['r', 0, 0], ['u', True, ['r', 0]], ['i', 0, 0, 1]]

    def paths(tree, prefix=()):
        yield prefix
        if isinstance(tree, list):
            for i, child in enumerate(tree):
                yield from paths(child, prefix + (i,))

    for _ in range(1200):
        cert = copy.deepcopy(rng.choice(deterministic))
        path = rng.choice(list(paths(cert['proof'])))
        replacement = copy.deepcopy(rng.choice(leaves))
        if not path:
            cert['proof'] = replacement
        else:
            at = cert['proof']
            for index in path[:-1]:
                at = at[index]
            at[path[-1]] = replacement
        explicit = accepted(modules['deterministic_explicit'], cert)
        implicit = accepted(modules['deterministic_implicit'], cert)
        if explicit != implicit:
            raise AssertionError(('Scope-removal mutation disagreement', cert))
        if explicit:
            accepted_mutations += 1
            if cert['goal'][0] == '=':
                if evaluate(cert['goal'][1]) != evaluate(cert['goal'][2]):
                    raise AssertionError(('False equation accepted after mutation', cert))
        mutations += 1

    # Force false closed conclusions independently of proof shape.
    for cert in deterministic:
        cert = copy.deepcopy(cert)
        cert['goal'] = ['=', 0, ['s', 0]]
        if accepted(modules['deterministic_explicit'], cert) or accepted(modules['deterministic_implicit'], cert):
            raise AssertionError('False conclusion accepted')

    with ThreadPoolExecutor(max_workers=8) as pool:
        records = list(pool.map(invoke, jobs))
    for row in records:
        if row['accepted'] != row['expected']:
            raise AssertionError(('Unexpected CLI result', row))
    result = {'status': 'passed', 'python': sys.version,
              'fixtures': len(manifest), 'scope_invariant_calls': calls,
              'closed_equations_evaluated': checked_equations,
              'mutations_compared': mutations, 'accepted_mutations': accepted_mutations,
              'false_conclusions_rejected': len(deterministic),
              'cli_runs': len(records),
              'metrics': [measure(name) for name in names], 'records': records,
              'limits': 'Finite tests supplement structural invariant and metatheory; no global semantic verification.'}
    (HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    main()
