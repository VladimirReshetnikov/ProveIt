"""Measure complete checkers; this script is not part of their trusted code."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import sys
import tokenize

ROOT = Path(__file__).resolve().parent.parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
           tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
EXPECTED = {
    'code/checker_tokens302.py': (302, 352, 646),
    'code/checker_ast340.py': (314, 340, 681),
    'code/checker_bytes584.py': (311, 362, 584),
    'code/checker_entry_tokens304.py': (304, 349, 646),
    'reference/checkers/strict_tokens306.py': (306, 362, 668),
    'reference/checkers/strict_ast348.py': (330, 348, 681),
    'reference/checkers/strict_bytes589.py': (324, 367, 589),
    'reference/checkers/compact_tokens239.py': (239, 261, 553),
    'reference/checkers/compact_ast255.py': (245, 255, 580),
    'reference/checkers/compact_bytes461.py': (267, 298, 461),
}


def measure(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw.decode('utf-8'))) + '\n').encode('utf-8')
    tokens = sum(tok.type not in IGNORED for tok in
                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return {
        'path': path.relative_to(ROOT).as_posix(),
        'tokens': tokens,
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'normalized_bytes': len(normalized),
        'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def main():
    rows = [measure(ROOT / path) for path in EXPECTED]
    mismatches = []
    for row in rows:
        actual = (row['tokens'], row['ast_nodes'], row['normalized_bytes'])
        if actual != EXPECTED[row['path']]:
            mismatches.append({'path': row['path'], 'expected': EXPECTED[row['path']],
                               'actual': actual})
    result = {'python': sys.version, 'normalization': 'ast.unparse + one LF',
              'rows': rows, 'mismatches': mismatches,
              'old_strict_envelope': [306, 348, 589],
              'new_strict_envelope': [302, 340, 584],
              'entry_only_envelope': [304, 340, 584],
              'compact_cross_contract_extrema': [239, 255, 461]}
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    for row in rows:
        print(f"{row['path']}: {row['tokens']}/{row['ast_nodes']}/{row['normalized_bytes']}")
    if mismatches:
        print('Measurements differ; use CPython 3.12.14 for the recorded normalization.')
        raise SystemExit(1)


if __name__ == '__main__':
    main()
