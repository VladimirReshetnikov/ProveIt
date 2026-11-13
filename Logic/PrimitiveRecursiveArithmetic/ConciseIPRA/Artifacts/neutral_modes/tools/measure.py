"""Measure complete source modules with the repository's normalization."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent.parent
SKIP = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}

class DropDocstrings(ast.NodeTransformer):
    def generic_visit(self, node):
        super().generic_visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.body:
            first = node.body[0]
            if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant) and isinstance(first.value.value, str):
                node.body.pop(0)
        return node

def normalized_tree(path):
    return DropDocstrings().visit(ast.parse(path.read_text()))

def measure(path):
    tree = normalized_tree(path)
    source = ast.unparse(tree) + '\n'
    data = source.encode('utf-8')
    return {'file': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)), 'normalized_bytes': len(data),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
            'normalized_sha256': hashlib.sha256(data).hexdigest(),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'normalized_ast_sha256': hashlib.sha256(ast.dump(tree, include_attributes=False).encode()).hexdigest()}

def main():
    paths = sorted((ROOT / 'code').glob('checker_*.py')) + sorted((ROOT / 'controls').glob('*.py'))
    rows = [measure(p) for p in paths]
    report = {'normalization_reference': 'CPython 3.12.14', 'python': sys.version,
              'runtime_matches_reference': platform.python_version() == '3.12.14',
              'zlib_runtime': zlib.ZLIB_RUNTIME_VERSION, 'programs': rows,
              'note': 'Gzip is informational. All coordinates count the entire standalone module.'}
    output = ROOT / 'evidence/measurements.json'
    if '--check' in sys.argv:
        old = json.loads(output.read_text())
        if report['programs'] != old['programs']:
            raise SystemExit('Measurements differ; use CPython 3.12.14 and inspect modified sources.')
    else:
        output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'runtime_matches_reference': report['runtime_matches_reference'],
                      'programs': [{k:r[k] for k in ['file','tokens','ast_nodes','normalized_bytes']} for r in rows]}, indent=2))

if __name__ == '__main__':
    main()
