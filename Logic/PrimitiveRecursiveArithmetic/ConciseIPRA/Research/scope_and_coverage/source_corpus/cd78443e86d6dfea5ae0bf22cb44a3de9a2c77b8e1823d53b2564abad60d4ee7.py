"""Whole-source measurements; no proof checking code imports this file."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent


class RemoveDocstrings(ast.NodeTransformer):
    def visit(self, node):
        node = super().visit(node)
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
            body = node.body
            if body and isinstance(body[0], ast.Expr):
                value = body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body = body[1:]
        return node


def metrics(path):
    raw = path.read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(raw.decode('utf-8')))
    ast.fix_missing_locations(tree)
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    count = sum(item.type not in ignored for item in
                tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    return {
        'path': str(path.relative_to(ROOT)),
        'raw_bytes': len(raw),
        'normalized_bytes': len(normalized),
        'tokens': count,
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw_bytes': len(compressed),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
    }, compressed


def main():
    rows = []
    for name in ('checker.py', 'checker_bytes.py', 'checker_joint.py'):
        for folder, prefix in (('reference', 'incumbent_'), ('code', '')):
            path = ROOT / folder / (prefix + name)
            row, compressed = metrics(path)
            rows.append(row)
            if folder == 'code':
                path.with_suffix('.py.gz').write_bytes(compressed)
    result = {
        'python': platform.python_version(), 'implementation': platform.python_implementation(),
        'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': 'Remove genuine docstrings, ast.unparse, append one newline; entire module.',
        'gzip': 'gzip.compress(raw_source, compresslevel=9, mtime=0), including wrapper',
        'programs': rows,
    }
    (ROOT / 'evidence' / 'measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    current = [r for r in rows if r['path'].startswith('code/')]
    labels = {'checker.py': 'New explicit list test', 'checker_bytes.py': 'New byte profile',
              'checker_joint.py': 'New generic traversal'}
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Complete program & Bytes & Tokens & AST & Gzip-9\\', r'\midrule',
             r'Incumbent separate minima &558&262&296&---\\']
    for row in current:
        name = Path(row['path']).name
        lines.append('{} &{}&{}&{}&{}\\\\'.format(labels[name], row['normalized_bytes'],
                     row['tokens'], row['ast_nodes'], row['gzip9_raw_bytes']))
    lines += [r'\midrule', 'New separate minima &{}&{}&{}&---\\\\'.format(
        min(r['normalized_bytes'] for r in current), min(r['tokens'] for r in current),
        min(r['ast_nodes'] for r in current)), r'\bottomrule', r'\end{tabular}', r'\end{center}']
    (ROOT / 'evidence' / 'metrics_table.tex').write_text('\n'.join(lines) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
