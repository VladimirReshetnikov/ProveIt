"""Reproduce whole-module measurements for the delivered and frozen programs."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    ('Raw evaluation discharge', 'raw/checker.py'),
    ('Matched raw separate rules', 'raw/control.py'),
    ('Zero-normal evaluation discharge', 'zero/code/checker.py'),
    ('Matched zero-normal separate rules', 'zero/code/control.py'),
    ('Incoming inferred-witness output control', 'reference/incoming_inferred_output_control.py'),
    ('Incoming inferred witness', 'reference/incoming_inferred_witness.py'),
    ('Incoming explicit clause discharge', 'reference/incoming_explicit_clause_discharge.py'),
]


def measure(path):
    original = path.read_bytes()
    tree = ast.parse(original.decode('utf-8'))
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    source = ast.unparse(tree) + '\n'
    data = source.encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(source).readline))
    return {'normalized_bytes': len(data), 'significant_tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(original).hexdigest(),
            'normalized_sha256': hashlib.sha256(data).hexdigest()}


def main():
    rows = [dict(name=name, path=path, **measure(ROOT / path)) for name, path in PROGRAMS]
    result = {'python': platform.python_version(),
              'convention': 'Complete module; remove actual docstrings; ast.unparse plus LF.',
              'rows': rows}
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    main()
