"""Measure complete modules; no helper is excluded from the trusted boundary."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = {
    'selected_uniform_R': ROOT / 'code/checker.py',
    'incoming_scalar_C5': ROOT / 'reference/scalar_incoming.py',
    'matched_scalar_walker': ROOT / 'reference/scalar_matched.py',
    'inherited_counter_forward': ROOT / 'reference/counter_forward.py',
}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode('utf-8'))
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.COMMENT}
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    record = {
        'path': str(path.relative_to(ROOT)),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in ignored for t in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'readable_bytes': len(raw),
        'readable_gzip9_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
    }
    return record, normalized


def main():
    out = ROOT / 'evidence/normalized'
    out.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, path in PROGRAMS.items():
        records[name], normalized = measure(path)
        (out / (name + '.py')).write_bytes(normalized)
        (out / (name + '.py.gz')).write_bytes(gzip.compress(normalized, compresslevel=9, mtime=0))
    result = {'python': platform.python_version(),
              'method': 'Remove the module docstring; ast.unparse; append one LF; count the entire module.',
              'gzip': 'RFC gzip, compression level 9, mtime 0; informational only.',
              'programs': records}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
