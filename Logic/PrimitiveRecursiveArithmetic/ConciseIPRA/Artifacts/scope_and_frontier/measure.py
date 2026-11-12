"""Reproduce the complete-module source measurements in the report."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    'reference/tokens248.py',
    'reference/ast270.py',
    'reference/bytes487.py',
    'reference/native629.py',
    'reference/strict646.py',
    'reference/strict654.py',
    'implementation/baseline492.py',
    'implementation/context_floor.py',
    'implementation/readable.py',
]
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
           tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}


def measure(relative):
    path = ROOT / relative
    raw = path.read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and type(node.body[0].value.value) is str):
                node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    compile(normalized, relative, 'exec')
    return {
        'path': relative,
        'significant_tokens': sum(token.type not in IGNORED for token in
            tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
    }


def main():
    rows = [measure(name) for name in PROGRAMS]
    report = {
        'python': platform.python_version(),
        'expected_measurement_version': '3.12.14',
        'method': 'remove genuine docstrings; ast.unparse plus LF',
        'upstream_commit': '36d37fc1071fe289371f6bcd7dcfa0eac593a5a6',
        'target_met': False,
        'coordinatewise_frontier_from_distinct_programs': [248, 270, 487],
        'rows': rows,
        'qualification': 'The compact, native-goal and strict interfaces '
                         'have different validation contracts.'
    }
    (ROOT / 'evidence/measurements.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
