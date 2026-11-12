"""Measure complete modules using the repository's normalized-source convention."""
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
from pathlib import Path
import tokenize


ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    ('Witness discharge', 'code/checker.py'),
    ('Matched separate elimination and transport', 'code/control_separate.py'),
    ('Witness discharge with fuel', 'code/checker_fuel.py'),
    ('Matched separate control with fuel', 'code/control_separate_fuel.py'),
    ('Incoming single evaluation', 'reference/single_evaluation.py'),
    ('Incoming variable substitution', 'reference/scalar_variable.py'),
    ('Published compact codec', 'reference/compact516.py'),
]


def main():
    rows = []
    excluded = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
                tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER,
                tokenize.COMMENT}
    for name, relative in PROGRAMS:
        path = ROOT / relative
        raw = path.read_bytes()
        tree = ast.parse(raw)
        if (tree.body and isinstance(tree.body[0], ast.Expr)
                and isinstance(tree.body[0].value, ast.Constant)
                and isinstance(tree.body[0].value.value, str)):
            tree.body.pop(0)
        normalized = (ast.unparse(tree) + '\n').encode()
        tokens = sum(t.type not in excluded for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline))
        compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
        rows.append(dict(
            program=name, path=relative, normalized_bytes=len(normalized),
            tokens=tokens, ast_nodes=sum(1 for _ in ast.walk(tree)),
            gzip9_bytes=len(compressed), raw_bytes=len(raw),
            raw_gzip9_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)),
            source_sha256=hashlib.sha256(raw).hexdigest(),
            normalized_sha256=hashlib.sha256(normalized).hexdigest()))
        if path.parent.name == 'code':
            (path.parent / (path.stem + '_normalized.py')).write_bytes(normalized)
            (path.parent / (path.stem + '_normalized.py.gz')).write_bytes(compressed)
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'metrics.json').write_text(json.dumps(dict(
        python=platform.python_version(),
        convention='remove module docstring; ast.unparse; one LF; gzip-9 mtime=0',
        rows=rows), indent=2) + '\n')
    with (evidence / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    for row in rows:
        print(row['program'], row['normalized_bytes'], row['tokens'],
              row['ast_nodes'], row['gzip9_bytes'])


if __name__ == '__main__':
    main()
