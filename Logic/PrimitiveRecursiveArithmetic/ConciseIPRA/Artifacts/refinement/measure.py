"""Reproduce full-module source measurements without importing checkers."""
from pathlib import Path
import ast
import hashlib
import io
import json
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'code/checker_compact.py': (271, 304, 488),
    'code/checker_strict.py': (423, 474, 855),
    'baseline/checker_495.py': (267, 299, 495),
    'baseline/checker_strict_862.py': (419, 469, 862),
    'baseline/checker_strict_869.py': (421, 471, 869),
    'baseline/checker_tokens_249.py': (249, 278, 607),
    'baseline/checker_ast_271.py': (255, 271, 606),
    'baseline/checker_native_643.py': (327, 375, 643),
}


def metric(path):
    raw = path.read_bytes()
    normalized = ast.unparse(ast.parse(raw.decode())) + '\n'
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
            tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    return {
        'path': str(path.relative_to(ROOT)),
        'significant_tokens': sum(t.type not in skip for t in
                                  tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode()),
        'source_bytes': len(raw),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
    }


def main():
    paths = sorted(ROOT.glob('code/*.py')) + sorted(ROOT.glob('baseline/*.py'))
    rows = [metric(path) for path in paths]
    mismatches = []
    for row in rows:
        actual = (row['significant_tokens'], row['ast_nodes'], row['normalized_bytes'])
        if row['path'] in EXPECTED and actual != EXPECTED[row['path']]:
            mismatches.append({'path': row['path'], 'expected': EXPECTED[row['path']],
                               'actual': actual})
        if row['path'] == 'code/two_field_reference.py' and row['normalized_bytes'] != 742:
            mismatches.append({'path': row['path'], 'expected_bytes': 742,
                               'actual_bytes': row['normalized_bytes']})
    result = {
        'python': sys.version,
        'reference_runtime': 'CPython 3.12.14',
        'normalization': 'ast.unparse(ast.parse(source)) followed by one newline',
        'scope': 'Complete standalone modules, including imports, JSON input and ACCEPT output',
        'measurements': rows,
        'expected_metrics_match': not mismatches,
        'mismatches': mismatches,
        'claim': 'Byte-only compact refinement; no joint improvement and no overall simplicity target achieved.',
    }
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    result = main()
    print(json.dumps(result, indent=2))
    if not result['expected_metrics_match']:
        raise SystemExit(1)
