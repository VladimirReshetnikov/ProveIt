"""Measure complete standalone modules under one reproducible convention."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parents[1]
FILES = [
    'code/checker.py',
    'code/checker_backward_name.py',
    'code/control_witness.py',
    'code/control_name.py',
    'code/checker_fuel.py',
    'code/control_witness_fuel.py',
    'code/control_name_fuel.py',
    'reference/parameter_intro_checker.py',
    'reference/uniform_recursion_checker.py',
    'reference/compact508.py',
]


class RemoveDocumentation(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
            node.body.pop(0)
        return node
    visit_Module = strip
    visit_FunctionDef = strip
    visit_AsyncFunctionDef = strip
    visit_ClassDef = strip


def measure(path):
    source = path.read_bytes()
    tree = RemoveDocumentation().visit(ast.parse(source))
    normalized = ast.unparse(tree) + '\n'
    significant = [t for t in tokenize.generate_tokens(io.StringIO(normalized).readline)
                   if t.type not in (tokenize.ENCODING, tokenize.ENDMARKER,
                                     tokenize.NEWLINE, tokenize.NL,
                                     tokenize.INDENT, tokenize.DEDENT,
                                     tokenize.COMMENT)]
    return {
        'normalized_bytes': len(normalized.encode('utf-8')),
        'significant_tokens': len(significant),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_bytes': len(gzip.compress(normalized.encode('utf-8'), compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode('utf-8')).hexdigest(),
    }


if __name__ == '__main__':
    result = {
        'python': platform.python_version(),
        'convention': 'Complete standalone source; docstrings/comments removed; ast.unparse plus one LF. Tokens exclude layout/comments. AST includes operator/context nodes. Gzip is informational.',
        'files': {name: measure(ROOT / name) for name in FILES},
        'interpretation': 'Matched supplied-witness deletion improves all three primary coordinates. Export improves bytes only against parameter_intro; the backward Name variant improves bytes, tokens and AST nodes against that incumbent. The compact 508-byte artifact has a different input/proof protocol and remains smaller.',
    }
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    for name, row in result['files'].items():
        print(name, row['normalized_bytes'], row['significant_tokens'], row['ast_nodes'])
