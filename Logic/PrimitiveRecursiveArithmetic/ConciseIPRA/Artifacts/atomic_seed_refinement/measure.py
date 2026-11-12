#!/usr/bin/env python3
"""Measure complete acceptance modules; comments and layout are not tokens."""
import ast
import hashlib
import io
import json
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXCLUDED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
FILES = [
    'reference/compact_tokens_248.py', 'reference/compact_ast_270.py',
    'reference/compact_479.py', 'reference/native_goal_643.py',
    'code/native_goal_checker.py', 'reference/native_strict_637.py',
    'code/native_strict_checker.py', 'code/atomic_seed_checker.py',
    'reference/atomic_raw_control.py',
]

def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode('utf-8'))
    normalized = ast.unparse(tree) + '\n'
    tokens = tokenize.generate_tokens(io.StringIO(normalized).readline)
    return {
        'significant_tokens': sum(t.type not in EXCLUDED for t in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_utf8_bytes': len(normalized.encode('utf-8')),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode('utf-8')).hexdigest(),
    }

def main():
    result = {'python': sys.version, 'normalization': 'ast.unparse + one LF',
              'files': {name: measure(ROOT / name) for name in FILES
                        if (ROOT / name).is_file()}}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    for name, data in result['files'].items():
        print(f"{name}: {data['significant_tokens']} tokens / "
              f"{data['ast_nodes']} AST nodes / {data['normalized_utf8_bytes']} bytes")

if __name__ == '__main__':
    main()
