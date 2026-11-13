"""Reproduce the measured refinement and its finite regression evidence.

This is a test driver, not part of the measured/trusted proof checker.
"""
import ast
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
OMIT = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
EXPECTED = {
    'code/checker304.py': (304, 361, 705),
    'benchmarks/strict_tokens306.py': (306, 362, 668),
    'benchmarks/strict_ast348.py': (330, 348, 681),
    'benchmarks/strict_bytes589.py': (324, 367, 589),
    'benchmarks/strict_joint313_353.py': (313, 353, 701),
    'benchmarks/compact_tokens239.py': (239, 261, 549),
    'benchmarks/compact_ast255.py': (245, 255, 580),
    'benchmarks/compact_bytes461.py': (267, 298, 461),
}


def measure(name):
    raw = (ROOT / name).read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + '\n').encode()
    counts = (
        sum(t.type not in OMIT for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        sum(1 for _ in ast.walk(ast.parse(normalized))),
        len(normalized),
    )
    if counts != EXPECTED[name]:
        raise AssertionError((name, counts, EXPECTED[name]))
    return dict(file=name, tokens=counts[0], ast_nodes=counts[1],
                normalized_bytes=counts[2],
                gzip9_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                source_sha256=hashlib.sha256(raw).hexdigest(),
                normalized_sha256=hashlib.sha256(normalized).hexdigest())


def run(job):
    case, name, optimized = job
    process = subprocess.run(
        [sys.executable, *(['-O'] if optimized else []), str(ROOT / name)],
        input=json.dumps(case['certificate']), text=True,
        capture_output=True, timeout=20,
    )
    accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
    return dict(case=case['name'], checker=name, optimized=optimized,
                expected=case['expected'], accepted=accepted,
                error=None if process.returncode == 0 else process.stderr.splitlines()[-1])


def main():
    metrics = [measure(name) for name in EXPECTED]
    cases = json.loads((ROOT / 'fixtures/three_field_cases.json').read_text())['cases']
    names = ['benchmarks/strict_tokens306.py', 'code/checker304.py']
    jobs = [(case, name, opt) for case in cases for name in names for opt in (False, True)]
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if r['accepted'] != r['expected']]
    receipt = dict(
        status='FAIL' if failures else 'PASS', python=platform.python_version(),
        commit='7a7633980dbca7f599322a5e7f1e65fb1cddb7c8',
        cases=len(cases), positive_cases=sum(c['expected'] for c in cases),
        negative_cases=sum(not c['expected'] for c in cases),
        isolated_executions=len(results), metrics=metrics,
        failures=failures, results=results,
        scope='Finite regression evidence, not formal verification. Ideal finite-resource semantics underlies the written proof.',
    )
    (ROOT / 'evidence/verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
