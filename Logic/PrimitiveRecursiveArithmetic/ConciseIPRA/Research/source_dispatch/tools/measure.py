"""Reproduce complete-module measurements; only genuine docstrings are removed.

Metric convention inherited from ProveIt ConciseIPRA, pinned in evidence/snapshot.json.
Uses symbolic tokenize constants (important with Python 3.12's new token IDs).
Gzip-9 is informational, not an optimization objective.
"""
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node

    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = clean


def measure(path):
    raw = path.read_bytes()
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw)))
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'path': str(path.relative_to(ROOT)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'raw_bytes': len(raw),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in IGNORED for t in
                                  tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def results():
    selected = [measure(ROOT / 'code' / name) for name in
                ('checker.py', 'checker_bytes.py', 'checker_tokens.py')]
    baseline = [measure(p) for p in sorted((ROOT / 'reference/checkers').rglob('*.py'))]
    return {
        'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'convention': 'Complete module; strip genuine docstrings; ast.unparse plus newline.',
        'selected': selected, 'baseline': baseline,
        'baseline_minima': {key: min(r[key] for r in baseline) for key in
                            ('normalized_bytes', 'significant_tokens', 'ast_nodes')},
        'selected_minima': {key: min(r[key] for r in selected) for key in
                            ('normalized_bytes', 'significant_tokens', 'ast_nodes')},
    }


if __name__ == '__main__':
    print(json.dumps(results(), indent=2))
