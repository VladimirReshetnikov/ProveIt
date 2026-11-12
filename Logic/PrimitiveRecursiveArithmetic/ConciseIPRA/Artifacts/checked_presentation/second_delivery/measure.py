"""Reproduce the repository's source metrics without executing measured code."""
import ast
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
           tokenize.DEDENT, tokenize.COMMENT, tokenize.ENDMARKER}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
            if not node.body and not isinstance(node, ast.Module):
                node.body = [ast.Pass()]
        return node

    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def measure(data):
    source = data.decode('utf-8') if isinstance(data, bytes) else data
    tree = StripDocstrings().visit(ast.parse(source))
    normalized = ast.unparse(tree) + '\n'
    return {
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'normalized_sha256': hashlib.sha256(normalized.encode('utf-8')).hexdigest(),
        'source_sha256': hashlib.sha256(source.encode('utf-8')).hexdigest(),
    }


def main():
    paths = sorted((ROOT / 'code').glob('checker_*.py'))
    paths += sorted((ROOT / 'controls').glob('*.py'))
    rows = [{'path': str(p.relative_to(ROOT)), **measure(p.read_bytes())} for p in paths]
    result = {'python': sys.version, 'definition': 'Strip actual docstrings; ast.unparse plus one LF; count significant tokens and all ast.walk nodes.', 'programs': rows}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    for row in rows:
        print(f"{row['tokens']:4} {row['ast_nodes']:4} {row['normalized_bytes']:5}  {row['path']}")


if __name__ == '__main__':
    main()
