"""Reproduce whole-program size coordinates; no checker imports this module."""
import ast
import csv
import gzip
import hashlib
import io
import json
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    ('reference/source_dispatch/code/checker_bytes.py', 'source bytes'),
    ('reference/source_dispatch/code/checker_tokens.py', 'source tokens'),
    ('reference/source_dispatch/code/checker.py', 'source AST'),
    ('reference/guarded_core/code/checker_bytes.py', 'guarded bytes'),
    ('reference/guarded_core/code/checker_tokens.py', 'guarded tokens'),
    ('reference/guarded_core/code/checker_ast.py', 'guarded AST'),
    ('code/checker_bytes.py', 'protected bytes'),
    ('code/checker_tokens.py', 'protected tokens'),
    ('code/checker_ast.py', 'protected AST'),
    ('code/readable_checker.py', 'readable expansion'),
    ('code/strict_checker.py', 'strict public-goal parser'),
]


class RemoveDocstrings(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node
    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = strip


def measurement(path, label=''):
    raw = path.read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(raw))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    significant = [t for t in tokenize.tokenize(io.BytesIO(normalized).readline)
                   if t.type not in ignored]
    return dict(label=label, raw_bytes=len(raw), normalized_bytes=len(normalized),
                tokens=len(significant), ast_nodes=sum(1 for _ in ast.walk(tree)),
                gzip9_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                raw_gzip9_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)),
                sha256=hashlib.sha256(raw).hexdigest()), normalized


def main():
    output = ROOT / 'evidence'
    output.mkdir(exist_ok=True)
    gzip_directory = output / 'gzip'
    gzip_directory.mkdir(exist_ok=True)
    rows = []
    for relative, label in PROGRAMS:
        row, normalized = measurement(ROOT / relative, label)
        row['source'] = relative
        rows.append(row)
        (gzip_directory / (relative.replace('/', '__') + '.gz')).write_bytes(
            gzip.compress(normalized, compresslevel=9, mtime=0))
    coordinates = ('normalized_bytes', 'tokens', 'ast_nodes')
    baseline = {key: min(row[key] for row in rows[:6]) for key in coordinates}
    candidate = {key: min(row[key] for row in rows[6:9]) for key in coordinates}
    environment = dict(python=sys.version, zlib=zlib.ZLIB_RUNTIME_VERSION,
                       normalization='Remove actual docstrings; ast.unparse plus one LF.',
                       compression='gzip.compress(source, compresslevel=9, mtime=0), wrapper included')
    result = dict(environment=environment, programs=rows, baseline_envelope=baseline,
                  candidate_envelope=candidate,
                  caveat='Each envelope has three different programs. Gzip is informational only.')
    (output / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    with (output / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    main()
