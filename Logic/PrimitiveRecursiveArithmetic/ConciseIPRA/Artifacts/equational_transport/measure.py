"""Reproduce whole-module measurements of the selected comparison files."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {getattr(tokenize, name) for name in (
    'ENCODING', 'NL', 'NEWLINE', 'INDENT', 'DEDENT', 'COMMENT', 'ENDMARKER')}

def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            body = node.body
            if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
                del body[0]
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    return dict(file=str(path.relative_to(ROOT)), raw_bytes=len(raw),
                tokens=sum(token.type not in SKIP for token in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)), normalized_bytes=len(normalized),
                gzip9_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                sha256=hashlib.sha256(raw).hexdigest())

programs = [ROOT / name for name in (
    'reference/diagonal_newest.py', 'code/equation_back.py', 'code/crossed_back.py', 'code/source_liberal.py')]
programs += sorted((ROOT / 'reference' / 'frontier_sources').glob('*.py'))
report = dict(python=sys.version, protocol='Genuine docstrings removed; ast.unparse plus LF; whole standalone module; gzip level9 mtime0', programs=[measure(path) for path in programs])
(ROOT / 'evidence' / 'measurements.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
