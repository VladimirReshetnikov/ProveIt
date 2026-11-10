"""Whole-module source metrics; the measured programs are never executed."""
import ast
import gzip
import hashlib
import io
import tokenize

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

    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def measure(raw):
    tree = ast.fix_missing_locations(
        StripDocstrings().visit(ast.parse(raw.decode('utf-8'))))
    normal = (ast.unparse(tree) + '\n').encode('utf-8')
    count = sum(t.type not in IGNORED for t in
                tokenize.generate_tokens(io.StringIO(normal.decode()).readline))
    return {
        'sha256': hashlib.sha256(raw).hexdigest(),
        'raw_bytes': len(raw),
        'normalized_bytes': len(normal),
        'normalized_tokens': count,
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized_bytes': len(gzip.compress(normal, compresslevel=9, mtime=0)),
    }
