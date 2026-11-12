"""Measure complete acceptance modules, including their public drivers."""
import ast
import csv
import gzip
import io
import json
import platform
from pathlib import Path
import tokenize
import zlib

ROOT = Path(__file__).resolve().parents[1]
FILES = [
    ('Shipped six-rule', 6, 'comparison/canonical_checker.py'),
    ('Matched six-rule', 6, 'comparison/arity_current_control.py'),
    ('Five-rule', 5, 'code/arity_checker.py'),
]
IGNORED = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}


def normalized(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    return (ast.unparse(tree) + '\n').encode('utf-8')


def metrics(label, rules, path):
    source = normalized(ROOT / path)
    destination = (ROOT / path).with_suffix('.normalized.py')
    destination.write_bytes(source)
    return {
        'label': label, 'rules': rules, 'path': path,
        'tokens': sum(t.type not in IGNORED for t in tokenize.tokenize(io.BytesIO(source).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
        'normalized_bytes': len(source),
        'gzip9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
    }


def main():
    rows = [metrics(*row) for row in FILES]
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    report = {'python': platform.python_version(), 'zlib': zlib.ZLIB_VERSION,
              'normalization': 'Remove docstrings; ast.unparse; one LF',
              'gzip': {'compresslevel': 9, 'mtime': 0}, 'checkers': rows}
    (evidence / 'metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    with (evidence / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrrr}\toprule',
             r'Complete verifier & Rules & Tokens & AST & Bytes & Gzip 9\\\midrule']
    for row in rows:
        lines.append(f"{row['label']} & {row['rules']} & {row['tokens']:,} & {row['ast_nodes']:,} & {row['normalized_bytes']:,} & {row['gzip9_bytes']:,}" + r'\\')
    lines += [r'\bottomrule\end{tabular}', r'\end{center}']
    (evidence / 'metrics_table.tex').write_text('\n'.join(lines) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
