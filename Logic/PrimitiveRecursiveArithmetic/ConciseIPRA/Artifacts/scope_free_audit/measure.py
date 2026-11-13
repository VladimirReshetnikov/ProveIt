"""Reproduce the complete-module size measurements (CPython 3.12.14)."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
OMIT = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    # Only real docstrings are removed, never ordinary string constants.
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'path': str(path.relative_to(ROOT)),
        'tokens': sum(t.type not in OMIT for t in
                      tokenize.tokenize(io.BytesIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def main():
    paths = sorted((ROOT / 'code').glob('checker_*.py'))
    paths += sorted((ROOT / 'reference').glob('checker_*.py'))
    paths += [ROOT / 'scope_free/checker.py', ROOT / 'scope_free/control239.py']
    result = {'python': platform.python_version(),
              'normalization': 'ast.unparse after docstring removal, plus one LF',
              'measurements': [measure(p) for p in paths]}
    (ROOT / 'evidence/measurements.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
