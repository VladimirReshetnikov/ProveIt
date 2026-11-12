#!/usr/bin/env python3
"""Reproduce measurements and finite checks. Python 3.12.14 is the benchmark.

The tests support the implementation audit; they are not a proof of soundness,
bi-interpretability, or equivalence for all certificates.
"""
import ast
import builtins
import contextlib
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
FILES = [
    'reference/checkers/checker_tokens_256.py',
    'reference/checkers/checker_ast_278.py',
    'reference/checkers/checker_bytes_516.py',
    'code/checker_compact.py',
    'reference/checkers/checker_strict_control.py',
    'code/checker_strict.py',
]


def measure(path):
    source = path.read_text()
    normalized = ast.unparse(ast.parse(source)) + '\n'
    excluded = {
        tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
    }
    tokens = sum(t.type not in excluded for t in
                 tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {
        'tokens': tokens,
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'gzip_bytes_informational': len(gzip.compress(normalized.encode(), mtime=0)),
        'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
    }


COMPILED = {}


def accepts(path, payload, optimize=0):
    """Execute an unchanged standalone checker against a virtual stdin.

The only shim is open(0); the program's JSON parser and stdout contract are
unchanged. Every invocation gets fresh globals, functions and contexts.
"""
    key = (str(path), optimize)
    if key not in COMPILED:
        COMPILED[key] = compile(path.read_text(), str(path), 'exec', optimize=optimize)
    stream = io.StringIO(json.dumps(payload))
    output = io.StringIO()
    env_builtins = dict(vars(builtins))

    def stdin_open(fd, *args, **kwargs):
        if fd != 0 or args or kwargs:
            raise ValueError('Unexpected file operation')
        return stream

    env_builtins['open'] = stdin_open
    env = {'__builtins__': env_builtins, '__name__': '__main__'}
    try:
        with contextlib.redirect_stdout(output):
            exec(COMPILED[key], env)
    except Exception:
        return False
    return output.getvalue() == 'ACCEPT\n'


def random_tree(rng, depth=0):
    if depth >= 3 or rng.random() < 0.55:
        return rng.choice([-4, -2, -1, 0, 1, 2, 3, 5, 7, 9])
    return [random_tree(rng, depth + 1) for _ in range(rng.randrange(5))]


def main():
    metrics = {f: measure(ROOT / f) for f in FILES}
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    control = ROOT / 'reference/checkers/checker_bytes_516.py'
    candidate = ROOT / 'code/checker_compact.py'
    strict_control = ROOT / 'reference/checkers/checker_strict_control.py'
    strict_candidate = ROOT / 'code/checker_strict.py'
    regressions = []
    positive_payloads = []
    for case in cases:
        payload = json.loads((ROOT / 'fixtures' / case['file']).read_text())
        if case['expected']:
            positive_payloads.append(payload)
        results = {}
        for optimize in (0, 1):
            for label, path, strict in [
                ('control', control, False), ('candidate', candidate, False),
                ('strict_control', strict_control, True),
                ('strict_candidate', strict_candidate, True),
            ]:
                observed = accepts(path, payload, optimize)
                expected = case['expected'] and (not strict or case['public_goal'])
                assert observed == expected, (case['name'], label, optimize, observed)
                results[f'{label}_O{optimize}'] = observed
        regressions.append({'name': case['name'], 'expected': case['expected'],
                            'public_goal': case['public_goal'], 'results': results})

    # Actual subprocess checks supplement the in-process stdin harness.
    cli_results = []
    for name, expected in [('computation_zero_local.json', True),
                           ('unproved_contradiction.json', False)]:
        payload = (ROOT / 'fixtures' / name).read_bytes()
        for optimize in (False, True):
            for path in (control, candidate, strict_candidate):
                cmd = [sys.executable] + (['-O'] if optimize else []) + [str(path)]
                run = subprocess.run(cmd, input=payload, capture_output=True, timeout=10)
                ok = run.returncode == 0 and run.stdout == b'ACCEPT\n'
                assert ok == expected, (name, path.name, optimize)
                cli_results.append({'fixture': name, 'checker': str(path.relative_to(ROOT)),
                                    'optimized': optimize, 'accepted': ok})

    rng = random.Random(20261112)
    random_count = 1200
    old_only = 0
    new_accepts = 0
    goals = [p[-1] for p in positive_payloads] + [[0, [0]], 0, [], [0]]
    for _ in range(random_count):
        payload = [[random_tree(rng) for _ in range(4)]
                   for _ in range(rng.randrange(6))] + [rng.choice(goals)]
        old = accepts(control, payload)
        new = accepts(candidate, payload)
        assert not new or old, 'New acceptance absent from control'
        old_only += old and not new
        new_accepts += new

    # Alter known proofs, so this also explores states near successful traces.
    mutation_count = 600
    mutation_new_accepts = 0
    mutation_old_only = 0
    for _ in range(mutation_count):
        payload = json.loads(json.dumps(rng.choice(positive_payloads)))
        if len(payload) > 1:
            index = rng.randrange(len(payload) - 1)
            if rng.randrange(2):
                del payload[index]
            else:
                payload[index][rng.randrange(4)] = random_tree(rng)
        old = accepts(control, payload)
        new = accepts(candidate, payload)
        assert not new or old, 'Mutated proof accepted only by candidate'
        mutation_new_accepts += new
        mutation_old_only += old and not new

    malformed = [True, False, None, 0.0, 1.5, 'annotation', {'x': 0}]
    valid = json.loads((ROOT / 'fixtures/computation_zero_local.json').read_text())
    for value in malformed:
        assert not accepts(strict_candidate, [value] + valid)
    for payload in ([], [[0, [0]]], [0], [[]], [[True, True]]):
        assert not accepts(strict_candidate, payload)

    # A public-goal certificate that demonstrates strict raw-trace inclusion.
    # The control ignores an invalid image in an unused computation packet;
    # eager prevalidation rejects it. The goal still has a canonical proof.
    old_only_payload = json.loads((ROOT / 'fixtures/eager_control_only.json').read_text())
    for path in (control, strict_control):
        assert accepts(path, old_only_payload)
    for path in (candidate, strict_candidate):
        assert not accepts(path, old_only_payload)

    evidence = {
        'python': platform.python_version(),
        'benchmark_python': '3.12.14',
        'metrics': metrics,
        'regressions': regressions,
        'cli_checks': cli_results,
        'random_seed': 20261112,
        'random_certificates': random_count,
        'random_new_accepts': new_accepts,
        'random_control_only_accepts': old_only,
        'mutated_certificates': mutation_count,
        'mutated_new_accepts': mutation_new_accepts,
        'mutated_control_only_accepts': mutation_old_only,
        'strict_extra_malformed_checks': len(malformed) + 5,
        'explicit_control_only_certificate': 'fixtures/eager_control_only.json',
        'explicit_control_only_results': {'control': True, 'candidate': False,
                                          'strict_control': True, 'strict_candidate': False},
        'result': 'All assertions passed',
        'limits': 'Finite checks are not formal verification. General claims are written proofs.',
    }
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/results.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({k: v for k, v in evidence.items()
                      if k not in ('regressions', 'cli_checks')}, indent=2))


if __name__ == '__main__':
    main()
