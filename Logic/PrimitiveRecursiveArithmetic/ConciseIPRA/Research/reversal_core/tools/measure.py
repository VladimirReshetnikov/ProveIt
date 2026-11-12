"""Measure the complete comparison programs using the repository convention."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parents[1]


class RemoveDocstrings(ast.NodeTransformer):
    def generic_visit(self, node):
        super().generic_visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
        return node


def measure(path):
    original = path.read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(original.decode('utf-8')))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    omit = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {
        'file': str(path.relative_to(ROOT)),
        'tokens': sum(t.type not in omit for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode('utf-8')).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized),
        'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(original).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


if __name__ == '__main__':
    result = {
        'python': platform.python_version(),
        'normalization': 'Remove genuine docstrings; ast.unparse; one final newline',
        'gzip': 'level=9, mtime=0, no embedded filename',
        'programs': [measure(p) for folder in ('code', 'controls')
                     for p in sorted((ROOT / folder).glob('*.py'))],
    }
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    gzip_dir = ROOT / 'evidence/gzip'
    gzip_dir.mkdir(exist_ok=True)
    for entry in result['programs']:
        path = ROOT / entry['file']
        tree = RemoveDocstrings().visit(ast.parse(path.read_text()))
        normalized = (ast.unparse(tree) + '\n').encode()
        (gzip_dir / (path.stem + '.py.gz')).write_bytes(
            gzip.compress(normalized, compresslevel=9, mtime=0))
    print(json.dumps({'python': result['python'], 'programs': len(result['programs']),
                      'metrics': 'evidence/metrics.json'}))
