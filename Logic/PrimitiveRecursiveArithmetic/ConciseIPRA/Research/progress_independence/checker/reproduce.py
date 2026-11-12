"""Measure the whole modules and replay the selected finite certificates."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORE = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
          tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROGRAMS = {
    'control': 'reference/checker_506.py',
    'parity': 'code/checker_parity.py',
    'compact': 'code/checker_compact.py',
    'strict': 'code/checker_strict.py',
}
TOKEN_PROGRAMS = {
    'tokens_control': 'reference/checker_tokens_253.py',
    'tokens': 'code/checker_tokens.py',
}


def measure(path):
    raw = path.read_bytes()
    source = ast.unparse(ast.parse(raw)) + '\n'
    return {
        'tokens': sum(t.type not in IGNORE for t in
                      tokenize.generate_tokens(io.StringIO(source).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
        'normalized_bytes': len(source.encode()),
        'sha256': hashlib.sha256(raw).hexdigest(),
    }


def main():
    raw = (ROOT / PROGRAMS['control']).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw)
    if blob.hexdigest() != 'a0af7afb236b530eb30c63c5ab788151024271b7':
        raise ValueError('The frozen control differs from its Git blob')
    metrics = {name: measure(ROOT / path) for name, path in
               (PROGRAMS | TOKEN_PROGRAMS).items()}
    receipts = []
    for case in json.loads((ROOT / 'fixtures/cases.json').read_text()):
        payload = (ROOT / 'fixtures' / case['name']).read_bytes()
        for optimized in (False, True):
            for name, path in PROGRAMS.items():
                command = [sys.executable] + (['-O'] if optimized else [])
                result = subprocess.run(command + [str(ROOT / path)],
                                        input=payload, capture_output=True,
                                        timeout=20)
                actual = result.returncode == 0 and result.stdout == b'ACCEPT\n'
                receipts.append({'fixture': case['name'], 'program': name,
                                 'optimized': optimized, 'expected': case[name],
                                 'actual': actual})
    for case in json.loads((ROOT / 'fixtures_tokens/cases.json').read_text()):
        payload = (ROOT / 'fixtures_tokens' / case['name']).read_bytes()
        for optimized in (False, True):
            for name, path in TOKEN_PROGRAMS.items():
                command = [sys.executable] + (['-O'] if optimized else [])
                result = subprocess.run(command + [str(ROOT / path)],
                                        input=payload, capture_output=True,
                                        timeout=20)
                actual = result.returncode == 0 and result.stdout == b'ACCEPT\n'
                receipts.append({'fixture': case['name'], 'program': name,
                                 'optimized': optimized,
                                 'expected': case['expected'], 'actual': actual})
    failures = [r for r in receipts if r['actual'] != r['expected']]
    report = {'python': platform.python_version(), 'metrics': metrics,
              'process_executions': len(receipts), 'failures': failures,
              'results': receipts}
    (ROOT / 'evidence/results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
