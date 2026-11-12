"""Offline verification of saved complete-program fixtures and source sizes."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent.parent


def main():
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    metrics = json.loads((ROOT / 'evidence/checker_metrics.json').read_text())
    rows = []
    for row in metrics:
        source = (ROOT / row['file']).read_bytes()
        tree = ast.parse(source)
        normalized = (ast.unparse(tree) + '\n').encode()
        tokens = [t for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
                  if t.type not in (tokenize.ENCODING, tokenize.ENDMARKER,
                                    tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
                                    tokenize.DEDENT, tokenize.COMMENT)]
        actual = dict(raw_bytes=len(source), normalized_bytes=len(normalized),
                      normalized_tokens=len(tokens), ast_nodes=len(list(ast.walk(tree))),
                      gzip9_raw=len(gzip.compress(source, compresslevel=9, mtime=0)),
                      gzip9_normalized=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                      sha256=hashlib.sha256(source).hexdigest())
        for key, value in actual.items():
            if value != row[key]:
                raise ValueError((row['file'], key, value, row[key]))
        if gzip.decompress((ROOT / (row['file'] + '.gz')).read_bytes()) != source:
            raise ValueError('Bad compressed source: ' + row['file'])
    for checker, tests in cases.items():
        for test in tests:
            for optimized in (False, True):
                result = subprocess.run([sys.executable] + (['-O'] if optimized else []) +
                                        [str(ROOT / checker)], input=json.dumps(test['packet']),
                                        text=True, capture_output=True, timeout=12)
                accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
                passed = accepted == test['accept']
                if not accepted:
                    passed = passed and result.returncode != 0 and 'ACCEPT' not in result.stdout
                rows.append(dict(checker=checker, test=test['name'], optimized=optimized,
                                 passed=passed, accepted=accepted, expected=test['accept']))
        for data in ('', '{', 'null', '[]', '{}', '[null]', '[true]', '["a"]'):
            for optimized in (False, True):
                result = subprocess.run([sys.executable] + (['-O'] if optimized else []) +
                                        [str(ROOT / checker)], input=data,
                                        text=True, capture_output=True, timeout=12)
                accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
                rows.append(dict(checker=checker, test='malformed_' + repr(data),
                                 optimized=optimized, expected=False, accepted=accepted,
                                 passed=not accepted and result.returncode != 0
                                 and 'ACCEPT' not in result.stdout))
    failures = [r for r in rows if not r['passed']]
    print(json.dumps(dict(runs=len(rows), passed=len(rows)-len(failures), failures=failures), indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
