"""Finite regression checks for the full normalizer and proof compiler."""
import ast
import copy
import gzip
import importlib.util
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import checker as full
import compiler

ROOT = Path(__file__).resolve().parent
Z, V, ONE = compiler.Z, compiler.V, compiler.ONE


def random_term(rng, scope, depth):
    if depth == 0:
        return ['v', rng.randrange(scope)] if scope and rng.randrange(2) else Z
    tag = rng.randrange(4)
    if tag == 0:
        return random_term(rng, scope, 0)
    if tag == 1:
        return ['s', random_term(rng, scope, depth - 1)]
    return ['i', random_term(rng, scope, depth - 1),
            random_term(rng, scope, depth - 1),
            random_term(rng, scope + 1, depth - 1)]


def raw_walk(a, fn, depth=0):
    if a[0] == 'v':
        return fn(a[1], depth)
    increments = {'i': [0, 0, 1], 'q': [1], 'd': [2]}.get(a[0], [0] * len(a))
    return [a[0]] + [raw_walk(b, fn, depth + increments[j])
                     for j, b in enumerate(a[1:])]


def raw_shift(a, amount):
    return raw_walk(a, lambda i, d: ['v', i + amount if i >= d else i])


def raw_sub(a, t):
    return raw_walk(a, lambda i, d: ['v', i] if i < d else
                    raw_shift(t, d) if i == d else ['v', i - 1])


def value(a, env):
    if a[0] == 'v':
        return env[a[1]]
    if a[0] == 'z':
        return 0
    if a[0] == 's':
        return value(a[1], env) + 1
    count, seed = value(a[1], env), value(a[2], env)
    if count > 100:
        raise OverflowError('Finite semantic test cutoff')
    for _ in range(count):
        seed = value(a[3], [seed] + env)
    return seed


def run():
    rng = random.Random(20261111)
    counts = dict(idempotence=0, substitution_coherence=0,
                  standard_value=0, computation_equations=0)
    for _ in range(1000):
        a, t = random_term(rng, 3, 3), random_term(rng, 2, 3)
        na, nt = compiler.normalize(a), compiler.normalize(t)
        full.term(na, 3)
        full.term(nt, 2)
        assert compiler.normalize(na) == na
        counts['idempotence'] += 1
        assert compiler.normalize(raw_sub(a, t)) == full.sub(na, nt)
        counts['substitution_coherence'] += 1
        env = [rng.randrange(3) for _ in range(3)]
        try:
            assert value(a, env) == value(na, env)
            counts['standard_value'] += 1
        except OverflowError:
            pass
        counter, seed, body = (random_term(rng, 2, 2), random_term(rng, 2, 2),
                               random_term(rng, 3, 2))
        assert compiler.normalize(['i', Z, seed, body]) == compiler.normalize(seed)
        left = compiler.normalize(['i', ['s', counter], seed, body])
        right = compiler.normalize(raw_sub(body, ['i', counter, seed, body]))
        assert left == right
        counts['computation_equations'] += 2

    reference_path = ROOT / 'reference/zero_normal/checker.py'
    spec = importlib.util.spec_from_file_location('zero_normal_reference', reference_path)
    reference = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reference)
    translations = []
    for path in sorted((ROOT / 'reference/zero_normal/certificates').glob('*.json')):
        source = json.loads(path.read_text())
        reference.check(source)
        target = compiler.certificate(source)
        archived = json.loads((ROOT / 'examples' / (path.stem + '_full.json')).read_text())
        assert target == archived, path.name
        translations.append(dict(source=path.name, checked=True, archived_output_matches=True))

    records = []
    for path in sorted((ROOT / 'examples').glob('*.json')):
        expected = not path.name.startswith('reject_')
        for optimized in [False, True]:
            args = [sys.executable] + (['-O'] if optimized else [])
            result = subprocess.run(args + [str(ROOT / 'checker.py')],
                                    input=path.read_text(), text=True,
                                    capture_output=True, timeout=20)
            accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
            assert accepted == expected, (path.name, optimized, result.stderr)
            records.append(dict(name=path.name, optimized=optimized, accepted=accepted))
    metrics = {}
    for name, path in [('zero_normal_forward', reference_path), ('full_normal_forward', ROOT / 'checker.py')]:
        data = (ast.unparse(ast.parse(path.read_text())) + '\n').encode()
        ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT, tokenize.DEDENT,
                   tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
        metrics[name] = dict(raw_bytes=path.stat().st_size, normalized_bytes=len(data),
                             significant_tokens=sum(t.type not in ignored for t in
                                 tokenize.generate_tokens(io.StringIO(data.decode()).readline)),
                             ast_nodes=sum(1 for _ in ast.walk(ast.parse(data))),
                             gzip9_bytes=len(gzip.compress(data, compresslevel=9, mtime=0)))
    report = dict(finite_checks=counts, source_translations=len(translations),
                  translations=translations, metrics=metrics, cli_checks=len(records),
                  accepted=sum(x['accepted'] for x in records),
                  rejected=sum(not x['accepted'] for x in records), records=records)
    (ROOT / 'evidence/forward_validation.json').write_text(json.dumps(report, indent=2))
    print(json.dumps({k: v for k, v in report.items() if k not in ['records', 'translations']}, indent=2))


if __name__ == '__main__':
    run()
