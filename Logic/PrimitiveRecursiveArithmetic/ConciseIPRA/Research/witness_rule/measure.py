"""Measure whole source modules; compressed size is informational only."""
import ast
import gzip
import hashlib
import io
import json
import platform
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
           tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}


def metrics(source):
    tree = ast.parse(source)
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'sha256': hashlib.sha256(source).hexdigest(),
        'raw_bytes': len(source),
        'normalized_bytes': len(normalized),
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.tokenize(io.BytesIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw': len(gzip.compress(source, compresslevel=9, mtime=0)),
        'gzip9_normalized': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def measure():
    paths = sorted((ROOT / 'code').glob('*.py'))
    paths += sorted((ROOT / 'reference').glob('certified_zero_checker*.py'))
    rows = [{'path': str(p.relative_to(ROOT)), **metrics(p.read_bytes())} for p in paths]
    original = (ROOT / 'reference/certified_zero_checker_bytes.py').read_text()
    controls = {
        'baseline_invalid_image_only': original.replace('t=None', 't=0j'),
        'choice_with_None_default': (ROOT / 'code/checker_choice.py').read_text().replace('t=0j', 't=None'),
    }
    for name, text in controls.items():
        rows.append({'control': name, **metrics(text.encode())})
    return {
        'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'protocol': {
            'normalization': 'ast.unparse(ast.parse(raw)) + LF; no code or data excluded',
            'tokens': 'Python tokenize, excluding comments, encoding, layout, and endmarker',
            'ast': 'all ast.walk nodes, including expression contexts and operators',
            'gzip': 'gzip.compress(exact_source, compresslevel=9, mtime=0)',
            'runtime_boundary': 'CPython and the standard json library are shared with all baselines',
        },
        'programs': rows,
    }


if __name__ == '__main__':
    result = measure()
    if '--write' in sys.argv:
        (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
        for p in (ROOT / 'code').glob('checker*.py'):
            p.with_suffix('.py.gz').write_bytes(gzip.compress(p.read_bytes(), compresslevel=9, mtime=0))
    print(json.dumps(result, indent=2))
