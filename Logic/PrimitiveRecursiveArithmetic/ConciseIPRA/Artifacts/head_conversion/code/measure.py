"""Measure complete modules with the repository's CPython normalization."""
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class StripDocstrings(ast.NodeTransformer):
    def generic_visit(self, node):
        node = super().generic_visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
        return node


def measure(path):
    raw = path.read_bytes()
    tree = StripDocstrings().visit(ast.parse(raw.decode('utf-8')))
    source = ast.unparse(tree) + '\n'
    data = source.encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(source).readline))
    return {'file': str(path.relative_to(ROOT)), 'tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_bytes': len(data), 'gzip9_bytes': len(gzip.compress(data, mtime=0)),
            'raw_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(data).hexdigest()}


def run():
    files = ['code/head_checker.py', 'code/full_checker.py',
             'reference/incumbent_tokens244.py', 'reference/incumbent_ast267.py',
             'reference/incumbent_bytes478.py']
    if (ROOT / 'code/compact477.py').exists():
        files.append('code/compact477.py')
    result = {'python': platform.python_version(),
              'normalization': 'strip docstrings; ast.unparse; one trailing LF; count entire module',
              'modules': [measure(ROOT / p) for p in files]}
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    run()
