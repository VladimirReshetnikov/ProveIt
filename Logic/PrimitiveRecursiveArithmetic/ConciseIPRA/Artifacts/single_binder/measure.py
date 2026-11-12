"""Measure complete modules with the pinned corpus convention."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROGRAMS = [
    'controls/tokens_control.py', 'code/tokens248.py',
    'controls/tokens_matched_line.py',
    'controls/ast_control.py', 'code/ast270.py',
    'controls/ast_matched_line.py',
    'controls/bytes_control.py', 'code/bytes488.py', 'code/bytes487.py',
    'code/strict_guarded.py', 'code/to_one_line.py',
    'controls/native666.py',
]


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and type(node.body[0].value.value) is str):
                node.body.pop(0)
    source = ast.unparse(tree) + '\n'
    compile(source, str(path), 'exec')
    return {'path': str(path.relative_to(ROOT)),
            'significant_tokens': sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    report = {'python': platform.python_version(),
              'normalization': 'remove genuine docstrings; ast.unparse plus one LF',
              'metrics': [measure(ROOT / name) for name in PROGRAMS],
              'limits': [
                  'Coordinate minima come from different complete programs.',
                  'Compact public-goal syntax is an input contract, not checked by these compact programs.',
                  'Token and AST reductions use one-line input framing; equally reframed controls tie.',
                  'The byte reductions preserve the existing multiline JSON interface.',
                  'No mathematical minimum or new arithmetic principle is claimed.',
              ]}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
