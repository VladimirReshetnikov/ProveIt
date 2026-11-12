"""Measure complete Python acceptance modules under the pinned convention."""
import ast
import io
import tokenize
from pathlib import Path


def measure(path):
    tree = ast.parse(Path(path).read_text(encoding='utf-8'))
    for node in ast.walk(tree):
        if (isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                and node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            del node.body[0]
    source = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(source).readline))
    return {'tokens': tokens, 'ast_nodes': len(list(ast.walk(ast.parse(source)))),
            'normalized_bytes': len(source.encode('utf-8'))}
