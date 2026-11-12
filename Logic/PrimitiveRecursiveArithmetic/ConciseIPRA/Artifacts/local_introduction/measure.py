"""Measure complete modules under the pinned normalization convention."""
import ast
import hashlib
import io
import json
import platform
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'code/diagonal_control.py': [870, 1022, 3274],
    'code/diagonal_newest.py': [862, 1011, 3245],
    'controls/tokens248.py': [248, 277, 609],
    'controls/ast270.py': [254, 270, 608],
    'controls/checker479.py': [272, 304, 479],
    'controls/checker637.py': [344, 392, 637],
    'controls/raw_alias_small.py': [773, 916, 2903],
}
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}


def measure(name):
    raw = (ROOT / name).read_bytes()
    source = ast.unparse(ast.parse(raw)) + '\n'
    normalized = source.encode('utf-8')
    counts = [sum(token.type not in SKIP for token in
                  tokenize.generate_tokens(io.StringIO(source).readline)),
              sum(1 for _ in ast.walk(ast.parse(source))), len(normalized)]
    return {'path': name, 'tokens': counts[0], 'ast_nodes': counts[1],
            'normalized_bytes': counts[2], 'expected': EXPECTED[name],
            'matches': counts == EXPECTED[name],
            'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def main():
    records = [measure(name) for name in EXPECTED]
    result = {'python': platform.python_version(), 'reference_python': '3.12.14',
              'method': 'Whole module: ast.unparse plus LF, then tokenize/ast.walk/UTF-8 length.',
              'records': records}
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    if not all(record['matches'] for record in records):
        raise SystemExit('Counts differ; check Python version and source identities.')


if __name__ == '__main__':
    main()
