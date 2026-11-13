"""Finite CLI checks and fully counted source metrics; outside the trusted core."""
import ast
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    original = path.read_bytes()
    tree = ast.parse(original)
    with_docstring = (ast.unparse(tree) + '\n').encode()
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    return {'file': str(path.relative_to(ROOT)),
            'significant_tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(normalized.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized),
            'normalized_gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'normalized_bytes_with_docstring': len(with_docstring),
            'normalized_gzip9_bytes_with_docstring': len(gzip.compress(with_docstring, compresslevel=9, mtime=0)),
            'raw_source_bytes': len(original),
            'raw_source_gzip9_bytes': len(gzip.compress(original, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(original).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def main():
    subprocess.run([sys.executable, str(ROOT / 'code/build_certificates.py')], check=True)
    checks = []
    for case in json.loads((ROOT / 'tests/cases.json').read_text()):
        path = ROOT / 'tests' / case['file']
        for optimized in (False, True):
            command = [sys.executable, '-I', '-S', '-B']
            if optimized:
                command.append('-O')
            command.append(str(ROOT / 'code/root_checker.py'))
            result = subprocess.run(command, input=path.read_bytes(), capture_output=True, timeout=30)
            accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
            checks.append({'fixture': case['file'], 'optimized': optimized,
                           'expected': case['expected'], 'accepted': accepted,
                           'passed': accepted == case['expected']})
    report = {'python': platform.python_version(), 'cli_runs': len(checks),
              'failed': [r for r in checks if not r['passed']], 'checks': checks,
              'metrics': [measure(ROOT / p) for p in ('code/root_checker.py', 'controls/scalar_bh3_checker.py')],
              'comparison_contract': 'Identical tagged-tree architecture and leaf/hint discipline; different raw recursors and computation-address grammars.',
              'formal_proof': False}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'checks'}, indent=2))
    if report['failed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
