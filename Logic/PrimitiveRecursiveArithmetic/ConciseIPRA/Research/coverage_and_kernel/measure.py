"""Measure complete Python modules using the inspected drafts' convention.

Only genuine docstrings are removed. The shared Python/JSON runtime is not
charged. Gzip level nine is reported as information, never optimized.
"""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize
import zlib

IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
           tokenize.ENDMARKER}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node

    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = clean


def metrics(raw):
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw)))
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'sha256': hashlib.sha256(raw).hexdigest(),
        'raw_bytes': len(raw),
        'normalized_bytes': len(normalized),
        'tokens': sum(t.type not in IGNORED for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def runtime():
    return {'python': platform.python_version(),
            'zlib': zlib.ZLIB_RUNTIME_VERSION}


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    paths = ([Path(p) for p in sys.argv[1:]] if len(sys.argv) > 1 else
             sorted((root / 'code').glob('*.py')) +
             sorted((root / 'reference').glob('*checker*.py')))
    rows = [{'path': str(p.resolve().relative_to(root)) if p.resolve().is_relative_to(root) else str(p),
             **metrics(p.read_bytes())} for p in paths]
    print(json.dumps({'runtime': runtime(), 'programs': rows}, indent=2))
