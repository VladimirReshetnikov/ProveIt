"""Measure complete acceptance modules using the repository convention."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

root = Path(__file__).resolve().parent
skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
rows = []
for relative in ('controls/compact479.py', 'code/compact478.py'):
    raw = (root / relative).read_bytes()
    normalized = ast.unparse(ast.parse(raw)) + '\n'
    rows.append({'path': relative,
                 'significant_tokens': sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
                 'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
                 'normalized_bytes': len(normalized.encode()),
                 'sha256': hashlib.sha256(raw).hexdigest(),
                 'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest()})
print(json.dumps({'python': platform.python_version(), 'modules': rows}, indent=2))
