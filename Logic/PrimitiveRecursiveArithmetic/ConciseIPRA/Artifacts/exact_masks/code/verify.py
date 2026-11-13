"""Reproduce exact-language checks, full executions, and frozen measurements.

The separate reference grammar is from the pinned exact-interface package.
It is evidence only: none of the measured checkers imports this file.
"""
import ast
import concurrent.futures
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


def term(a, available=()):
    if type(a) is int:
        return a == 1 or (a >= 3 and a % 2 == 1
                         and (a - 3) // 2 < len(available)
                         and available[(a - 3) // 2])
    if type(a) is not list:
        return False
    if len(a) == 1:
        return term(a[0], (False, False) + available)
    if len(a) == 3:
        return (term(a[0], (False,) + available)
                and term(a[1], (False,) + available)
                and term(a[2], (True,) + available))
    return False


def formula(a, available=()):
    if type(a) is not list:
        return False
    if len(a) == 1:
        return formula(a[0], (True, True) + available)
    if len(a) == 2:
        return term(a[0], available) and term(a[1], available)
    return False


def root_predicate(path):
    lam = next(n for n in ast.walk(ast.parse(path.read_text()))
               if isinstance(n, ast.Lambda))
    named = ast.fix_missing_locations(ast.NamedExpr(
        target=ast.Name(id='i', ctx=ast.Store()), value=copy.deepcopy(lam)))
    namespace = {'g': [], 'k': 0, 'v': 1, 'c': object()}
    opener = eval(compile(ast.Expression(body=named), '<measured-root-opener>', 'eval'), namespace)

    def valid(a):
        try:
            if str(a).strip('0123456789-[], '):
                return False
            return opener(a) == a
        except (TypeError, ValueError, IndexError, RecursionError):
            return False
    return valid


def grammar_cases():
    rng = random.Random(706)

    def raw(depth=0):
        if depth > 5 or rng.random() < .4:
            return rng.choice(list(range(-3, 21)) + [True, False, 1.0, None, '3', {}])
        return [raw(depth + 1) for _ in range(rng.randrange(5))]

    def canonical_term(mask, depth=0):
        if depth > 5 or rng.random() < .5:
            return rng.choice([1] + [3 + 2*j for j, bit in enumerate(mask) if bit])
        if rng.random() < .5:
            return [canonical_term([False, False] + mask, depth + 1)]
        return [canonical_term([False] + mask, depth + 1),
                canonical_term([False] + mask, depth + 1),
                canonical_term([True] + mask, depth + 1)]

    def canonical_formula(mask=(), depth=0):
        if depth > 4 or rng.random() < .7:
            return [canonical_term(list(mask)), canonical_term(list(mask))]
        return [canonical_formula([True, True] + list(mask), depth + 1)]

    cases = [raw() for _ in range(20000)] + [canonical_formula() for _ in range(10000)]
    scalars = list(range(-3, 21))
    cases += [[x, y] for x in scalars for y in scalars]
    cases += [[[x], [y]] for x in scalars for y in scalars]
    cases += [[[x, y, z], 1] for x in scalars for y in scalars for z in scalars]
    return cases


def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    skip = {tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
            tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
    return {'tokens': sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(source)))), 'bytes': len(source.encode()),
            'gzip9': len(gzip.compress(source.encode(), compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(source.encode()).hexdigest()}


def run(job):
    filename, name, data, expected, optimized = job
    result = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(ROOT / filename)],
                            input=data, text=True, capture_output=True, timeout=20)
    return {'file': filename, 'case': name, 'optimized': optimized, 'expected': expected,
            'accepted': result.returncode == 0 and result.stdout == 'ACCEPT\n'}


def main():
    manifest = json.loads((ROOT / 'metrics.json').read_text())
    grammar = grammar_cases()
    expected_grammar = [formula(a) for a in grammar]
    summaries = []
    jobs = []
    for profile in manifest['profiles']:
        filename = profile['file']
        actual_metrics = measure(ROOT / filename)
        for key, value in actual_metrics.items():
            if profile[key] != value:
                raise ValueError('Frozen metric/hash mismatch: ' + filename + '/' + key)
        valid = root_predicate(ROOT / filename)
        failures = [a for a, expected in zip(grammar, expected_grammar) if valid(a) != expected]
        cases = json.loads((ROOT / 'fixtures' / (profile['baseline'] + '.json')).read_text())['cases']
        for row in cases:
            for opt in (False, True):
                jobs.append((filename, row['name'], json.dumps(row['certificate']) + '\n', row['expected'], opt))

        seed = next(r['certificate'] for r in cases if r['name'] == 'direct_zero')
        literal = json.dumps(seed)
        expression = profile['reader'] != 'whole JSON'
        multiline = profile['reader'] == 'whole-document restricted expression'
        line_reader = profile['reader'] == 'one-line restricted expression'
        reader_cases = [('empty_document', '', False), ('empty_stack', '[]', False),
                        ('scalar_document', '0', False), ('outer_tuple', '0,0', False),
                        ('forbidden_name', 'open(0)', False),
                        ('forbidden_plus', literal + '+[]', False),
                        ('forbidden_comment', literal + '#', False),
                        ('subtraction_alias', literal.replace('1', '1-0', 1), expression),
                        ('double_negation_alias', literal.replace('1', '--1', 1), expression),
                        ('index_alias', literal.replace('1', '[0,1][1]', 1), expression),
                        ('pretty_document', json.dumps(seed, indent=2), multiline or not expression),
                        ('trailing_ignored_line', literal + '\nletters', line_reader)]
        for name, data, expected in reader_cases:
            for opt in (False, True):
                jobs.append((filename, 'reader_' + name, data + '\n', expected, opt))
        summaries.append({'file': filename, 'metrics': actual_metrics,
                          'grammar_cases': len(grammar), 'grammar_failures': failures[:20],
                          'canonical_positive_fixtures': sum(r['expected'] for r in cases)})

    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if r['accepted'] != r['expected']]
    receipt = {'python': sys.version, 'profiles': summaries,
               'grammar_comparisons': len(grammar) * len(summaries),
               'executions': len(results), 'failures': failures, 'results': results,
               'claim_boundary': 'Finite implementation checks supplement the written exact-mask and phase-simulation proofs; no fresh Lean verification is asserted.'}
    (ROOT / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'results'}, indent=2))
    if failures or any(r['grammar_failures'] for r in summaries):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
