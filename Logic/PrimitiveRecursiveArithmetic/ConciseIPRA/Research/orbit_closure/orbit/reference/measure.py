"""Reproduce normalized-source metrics for the matched complete kernels."""
from pathlib import Path
import ast
import gzip
import io
import json
import sys
import tokenize

root = Path(__file__).parent
ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
rows = []
for name in ('baseline_qi.py', 'scalar_ur.py'):
    tree = ast.parse((root / name).read_text())
    source = ast.unparse(tree) + '\n'
    data = source.encode()
    compressed = gzip.compress(data, compresslevel=9, mtime=0)
    (root / (name + '.normalized.py')).write_text(source)
    (root / (name + '.normalized.gz')).write_bytes(compressed)
    rows.append({'file': name, 'bytes': len(data),
                 'tokens': sum(t.type not in ignored for t in
                               tokenize.generate_tokens(io.StringIO(source).readline)),
                 'ast_nodes': sum(1 for _ in ast.walk(tree)),
                 'gzip9': len(compressed)})
result = {'python': sys.version, 'metrics': rows}
(root / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
