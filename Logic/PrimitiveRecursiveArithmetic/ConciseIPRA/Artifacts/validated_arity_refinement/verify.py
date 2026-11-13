"""Reproduce all three fully validated checker improvements."""
from pathlib import Path
import ast
import concurrent.futures
import json
import subprocess
import sys
import verify_byte as verify

HERE = Path(__file__).resolve().parent
PAIRS = [('controls/strict_tokens.py', 'code/checker_strict_tokens317.py'),
         ('controls/strict_ast.py', 'code/checker_strict_ast356.py')]


def run(job):
    case, checker, optimized = job
    p = subprocess.run([sys.executable, *(['-O'] if optimized else []),
                        str(HERE / checker)], input=json.dumps(case['certificate']),
                       text=True, capture_output=True, timeout=20)
    accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
    return dict(case=case['name'], checker=checker, optimized=optimized,
                expected=case['expected'], accepted=accepted)


def main():
    for control, candidate in PAIRS:
        source = (HERE / control).read_text()
        if source.count('g += [0]') != 1:
            raise AssertionError('Expected exactly one neutral extension')
        expected = source.replace('g += [0]', "g += b'\\x00'")
        if ast.dump(ast.parse(expected)) != ast.dump(ast.parse((HERE / candidate).read_text())):
            raise AssertionError('Candidate differs beyond neutral extension')
    cases = json.loads((HERE / 'fixtures/supply_cases.json').read_text())['cases']
    jobs = [(case, checker, optimized) for case in cases
            for pair in PAIRS for checker in pair for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if r['expected'] != r['accepted']]
    measurements = {p: verify.metrics(HERE / p) for pair in PAIRS for p in pair}
    receipt = dict(python=sys.version, cases=len(cases), process_executions=len(results),
                   measurements=measurements, failures=failures, results=results)
    (HERE / 'evidence/family_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)
    verify.main()


if __name__ == '__main__':
    main()
