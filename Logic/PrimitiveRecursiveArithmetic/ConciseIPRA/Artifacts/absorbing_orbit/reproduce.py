"""Reproduce new checker/arithmetic evidence and the standalone paper."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORE = {tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
          tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
EXPECTED = {
    'controls/checker_tokens.py': (244, 272, 608),
    'controls/checker_ast.py': (249, 267, 606),
    'controls/checker_bytes.py': (272, 304, 479),
    'controls/native607.py': (337, 383, 607),
    'checker/checkers/strict637.py': (344, 392, 637),
    'checker/checkers/strict632.py': (343, 390, 632),
}


def measure(path):
    raw = (ROOT / path).read_bytes()
    source = ast.unparse(ast.parse(raw)) + '\n'
    tree = ast.parse(source)
    result = (sum(t.type not in IGNORE for t in
                  tokenize.generate_tokens(io.StringIO(source).readline)),
              len(list(ast.walk(tree))), len(source.encode()))
    return {'path': path, 'tokens': result[0], 'ast_nodes': result[1],
            'normalized_bytes': result[2], 'expected': EXPECTED[path],
            'matches': result == EXPECTED[path],
            'sha256': hashlib.sha256(raw).hexdigest()}


def run(script, *args):
    subprocess.run([sys.executable, str(ROOT / script), *args],
                   cwd=ROOT, check=True)


def main():
    measures = [measure(name) for name in EXPECTED]
    if not all(item['matches'] for item in measures):
        raise ValueError('Metric mismatch: use the documented CPython 3.12.14')
    report = {'runtime': sys.version, 'measurements': measures,
              'current_compact_envelope': [244, 267, 479],
              'new_strict_envelope': [334, 387, 632],
              'envelopes_attained_by_single_program': False}
    (ROOT / 'evidence/reproduced_metrics.json').write_text(
        json.dumps(report, indent=2) + '\n')
    run('checker/verify_checker.py')
    run('mathematics/predecessor51.py')
    run('build.py', *(['--pdf'] if '--pdf' in sys.argv else []))
    print('All requested reproduction steps passed.')


if __name__ == '__main__':
    main()
