"""Reproduce complete-module source metrics for the selected comparisons."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
NAMES = ['native_original.py', 'native_goal_latest.py',
         'scalar_transport.py', 'scalar_latest.py']
EXCLUDED = {tokenize.COMMENT, tokenize.ENCODING, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
report = {'python': sys.version,
          'method': 'Complete module after ast.unparse(ast.parse(source)) plus LF; comments excluded by unparse, docstrings counted.',
          'programs': {}}
for name in NAMES:
    source = (ROOT / name).read_bytes()
    text = ast.unparse(ast.parse(source.decode())) + '\n'
    normalized = text.encode()
    report['programs'][name] = {
        'source_bytes': len(source),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'normalized_bytes': len(normalized),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
        'significant_tokens': sum(t.type not in EXCLUDED for t in tokenize.generate_tokens(io.StringIO(text).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(text)))),
        'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0))}
(ROOT / 'selected_metrics.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
