"""Reproduce complete-module metrics, including parser and validation."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
                tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    tokens = [t for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
              if t.type not in excluded]
    path.with_name(path.stem + '_normalized.py').write_bytes(normalized)
    return {'bytes': len(normalized), 'tokens': len(tokens),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def main():
    result = {'python': sys.version.split()[0], 'metric': 'Whole module, remove leading docstring, ast.unparse, one LF',
              'checker': measure(ROOT / 'checker.py'),
              'control': measure(ROOT / 'control.py')}
    result['saving'] = {k: result['control'][k] - result['checker'][k]
                        for k in ['bytes', 'tokens', 'ast_nodes', 'gzip9']}
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
