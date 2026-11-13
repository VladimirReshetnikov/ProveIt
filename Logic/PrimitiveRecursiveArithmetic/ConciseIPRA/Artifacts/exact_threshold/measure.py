"""Measure complete source modules without executing them (CPython 3.12.14)."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class RemoveDocstrings(ast.NodeTransformer):
    def _body(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            value = node.body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                node.body.pop(0)
        return node

    visit_Module = _body
    visit_FunctionDef = _body
    visit_AsyncFunctionDef = _body
    visit_ClassDef = _body


def measure(path):
    source = path.read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(source.decode()))
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'path': str(path.relative_to(ROOT)),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
        'tokens': sum(t.type not in SKIP for t in
                      tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'gzip9_bytes_information_only': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


paths = [ROOT/'code/checker.py', ROOT/'controls/intrinsic_checker.py']
paths += sorted((ROOT/'controls/frontier').glob('*.py'))
receipt = {'python': sys.version, 'modules': [measure(p) for p in paths],
           'qualification': 'Different controls have different input contracts; see report and baseline_audit.md.'}
(ROOT/'evidence/measured_controls.json').write_text(json.dumps(receipt, indent=2)+'\n')
for row in receipt['modules']:
    print(row['path'], row['tokens'], row['ast_nodes'], row['normalized_bytes'])
