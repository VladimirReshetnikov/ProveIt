"""Reproduce whole-module measurements; no checker imports are executed."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
FILES = [
    'baseline/compact_tokens239.py',
    'baseline/compact_ast255.py',
    'baseline/compact_bytes460.py',
    'baseline/strict_tokens302.py',
    'baseline/strict_ast340.py',
    'baseline/strict_bytes584.py',
    'baseline/exact_canonical1424.py',
    'refinement/checker581.py',
    'bundle/bundle_checker.py',
    'synthesis/synth.py',
]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}

def measure(name):
    raw = (ROOT / name).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode('utf-8')
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    return {
        'file': name,
        'raw_bytes': len(raw),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'gzip9_normalized_bytes': len(compressed),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'sha256_raw': hashlib.sha256(raw).hexdigest(),
        'sha256_normalized': hashlib.sha256(normalized).hexdigest(),
    }

if __name__ == '__main__':
    data = {'python': sys.version, 'normalization': 'ast.unparse + one LF',
            'gzip': 'level 9; mtime 0; normalized whole module',
            'measurements': [measure(name) for name in FILES]}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(data, indent=2) + '\n')
    for row in data['measurements']:
        print(row['file'], row['significant_tokens'], row['ast_nodes'],
              row['normalized_bytes'], row['gzip9_normalized_bytes'])
