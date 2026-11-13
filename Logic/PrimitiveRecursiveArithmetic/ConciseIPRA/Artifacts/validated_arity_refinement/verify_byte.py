"""Verify the exact arity-mode refinement of the supplied strict checker."""
from pathlib import Path
import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
BASE = HERE
CONTROL = BASE / 'controls/checker_strict599.py'
CANDIDATE = HERE / 'code/checker_strict597.py'


def metrics(path):
    tree = ast.parse(path.read_text())
    source = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(source.decode()).readline))
    return dict(tokens=tokens, ast_nodes=len(list(ast.walk(tree))),
                normalized_bytes=len(source),
                gzip9=len(gzip.compress(source, compresslevel=9, mtime=0)),
                normalized_sha256=hashlib.sha256(source).hexdigest())


def rotate(document):
    return [(r[1:] + r[:1] if isinstance(r, list) and len(r) == 4 else r)
            for r in document[:-1]] + document[-1:]


def run(job):
    case, checker, optimized = job
    p = subprocess.run([sys.executable, *(['-O'] if optimized else []),
                        str(checker)], input=json.dumps(rotate(case['certificate'])),
                       text=True, capture_output=True, timeout=20)
    accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
    return dict(case=case['name'], checker=checker.name, optimized=optimized,
                expected=case['expected'], accepted=accepted)


def main():
    old = CONTROL.read_text()
    new = CANDIDATE.read_text()
    expected = old.replace('v <= (len(a) in (1, 2 + d % 2))',
                           'len(a) ** v in (1, 2 + d % 2)')
    if ast.dump(ast.parse(expected)) != ast.dump(ast.parse(new)):
        raise AssertionError('Candidate differs beyond the stated rewrite')
    law_checks = 0
    for n in range(65):
        for d in range(-12, 25):
            for v in (0, 1):
                assert (v <= (n in (1, 2 + d % 2))) == (n ** v in (1, 2 + d % 2))
                law_checks += 1
    cases = json.loads((BASE / 'fixtures/strict_cases.json').read_text())['cases']
    jobs = [(case, checker, optimized) for case in cases
            for checker in (CONTROL, CANDIDATE) for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if r['expected'] != r['accepted']]
    receipt = dict(python=sys.version, scope='Exact rewrite plus inherited strict fixtures',
                   control=metrics(CONTROL), candidate=metrics(CANDIDATE),
                   arithmetic_law_checks=law_checks, cases=len(cases),
                   process_executions=len(results), failures=failures, results=results)
    (HERE / 'evidence/verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
