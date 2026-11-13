"""Evidence for the restricted expression reader; not trusted by the checker."""
import concurrent.futures
import json
from pathlib import Path
import random
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ALPHABET = '0123456789-[], '


def canonical_tree(value):
    return type(value) is int or type(value) is list and all(map(canonical_tree, value))


def expression(value, arithmetic=False):
    if type(value) is int:
        return str(value + 1) + '-1' if arithmetic else str(value)
    return '[' + ','.join(expression(x, arithmetic) for x in value) + ']'


def parse_expression(source):
    # This is the exact one-line reader. The filter is evaluated first.
    return (source.strip(ALPHABET) or eval(source)).pop.__self__


def fixtures():
    return json.loads((HERE / 'fixtures.json').read_text())


def reader_checks():
    rng = random.Random(672)
    def tree(depth=0):
        if depth > 4 or rng.random() < .55:
            return rng.randrange(-25, 26)
        return [tree(depth + 1) for _ in range(rng.randrange(5))]
    failures = []
    successes = 0
    for index in range(1000):
        value = [tree() for _ in range(rng.randrange(5))]
        for source in (expression(value), expression(value, True),
                       '[' + expression(value, True) + '][0]'):
            actual = parse_expression(source)
            if actual != value or not canonical_tree(actual):
                failures.append({'source': source, 'actual': actual})
            successes += 1
    rejected = ['', ' ', ',', '1,2', '[],', '[1][0,0]', '[1][[]]',
                '-[]', '[]-[]', '[1][1]', '[1][--2]', '[,]', '[01]',
                '[1.0]', '[True]', '[None]', "['x']", '[{}]', '[()]',
                '__import__("os")', '(lambda:0)()', 'open(0)',
                '().__class__', '[x for x in []]', '[0]*3', '[1+2]',
                '[1/1]', '[2**3]', '[0x1]', '[1e0]', '[1_0]', '[١]']
    for source in rejected:
        try:
            actual = parse_expression(source)
        except Exception:
            continue
        failures.append({'unexpectedly_accepted': source, 'actual': repr(actual)})
    return {'canonical_and_alternative_values': successes,
            'rejected_reader_strings': len(rejected), 'failures': failures}


def checker_checks():
    rows = fixtures()
    # Non-integer/list JSON values are rejected lexically by the new reader.
    seed = next(r['certificate'] for r in rows if r['expected'])
    jobs = []
    for row in rows:
        if not canonical_tree(row['certificate']):
            spellings = [json.dumps(row['certificate'])]
        else:
            e = expression(row['certificate'], True)
            spellings = [json.dumps(row['certificate']), e, '[' + e + '][0]']
        for spelling_index, source in enumerate(spellings):
            for optimized in (False, True):
                for checker in ('checker_exact_line_expression.py',
                                'checker_exact_document_expression.py'):
                    jobs.append({'name': row['name'], 'expected': row['expected'],
                                 'source': source, 'spelling': spelling_index,
                                 'optimized': optimized, 'checker': checker})
    attacks = ['1,2', '[],', '[1][0,0]', '__import__("os")',
               '().__class__', '[x for x in []]', 'open(0)', '[1]*3',
               '[1.0]', '[True]', '[None]', '[1e0]', '[0x1]', '[1_0]']
    attacks += [json.dumps(seed) + 'x', '[' + json.dumps(seed) + '][0,0]']
    for source in attacks:
        for checker in ('checker_exact_line_expression.py',
                        'checker_exact_document_expression.py'):
            jobs.append({'name': 'reader_attack', 'expected': False,
                         'source': source, 'spelling': 0,
                         'optimized': False, 'checker': checker})

    def run(job):
        process = subprocess.run([sys.executable,
                                  *(['-O'] if job['optimized'] else []),
                                  str(HERE / job['checker'])],
                                 input=job['source'] + '\n', text=True,
                                 capture_output=True, timeout=10)
        accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
        return {k: v for k, v in job.items() if k != 'source'} | {'accepted': accepted}
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(run, jobs))
    failures = [row for row in results if row['expected'] != row['accepted']]
    return {'executions': len(results), 'failures': failures, 'results': results}


if __name__ == '__main__':
    receipt = {'python': sys.version, 'reader': reader_checks(),
               'checker': checker_checks()}
    (HERE / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'reader': receipt['reader'],
                      'checker': {k: v for k, v in receipt['checker'].items()
                                  if k != 'results'}}, indent=2))
    if receipt['reader']['failures'] or receipt['checker']['failures']:
        raise SystemExit(1)
