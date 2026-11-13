"""Measure complete proposal and comparison modules, without executing them."""

import ast
import gzip
import hashlib
import io
import json
import platform
from pathlib import Path
import tokenize


MODULES = (
    'control_canonical_five.py',
    'control_counter_transport.py',
    'control_raw_ce5.py',
    'control_raw_two_case.py',
    'control_zero_normal_eval.py',
    'counter_eval.py',
)


def measure(path):
    source = path.read_bytes()
    tree = ast.parse(source.decode('utf-8'))
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    data = normalized.encode('utf-8')
    ignored = {
        tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
    }
    tokens = tokenize.generate_tokens(io.StringIO(normalized).readline)
    return {
        'normalized_bytes': len(data),
        'significant_tokens': sum(t.type not in ignored for t in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'normalized_sha256': hashlib.sha256(data).hexdigest(),
    }


def main():
    root = Path(__file__).resolve().parent
    result = {
        'python': platform.python_version(),
        'normalization': 'Remove module docstring; ast.unparse; one final LF',
        'programs': {name: measure(root / name) for name in MODULES},
    }
    serialized = json.dumps(result, indent=2) + '\n'
    evidence = root.parent / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'metrics.json').write_text(serialized, encoding='utf-8')
    print(serialized, end='')


if __name__ == '__main__':
    main()
