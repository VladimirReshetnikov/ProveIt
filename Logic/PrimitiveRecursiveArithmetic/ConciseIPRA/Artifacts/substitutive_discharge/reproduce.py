"""Replay delivered certificate checks and regenerate complete-module metrics."""
import ast
import gzip
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

root = Path(__file__).resolve().parent
for script in ['validation/canonical_validation.py', 'validation/control_translation.py',
               'raw_scalar/verify.py']:
    r = subprocess.run([sys.executable, str(root / script)], cwd=root, text=True,
                       capture_output=True)
    if r.returncode:
        print(r.stdout)
        print(r.stderr)
        raise SystemExit(r.returncode)
    print(script, 'PASS')

def measure(path):
    tree = ast.parse(path.read_text())
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    text = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
               tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'normalized_bytes': len(text.encode()),
            'significant_tokens': sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(text).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9': len(gzip.compress(text.encode(), compresslevel=9, mtime=0))}

result = {'python': platform.python_version(), 'programs': {}}
for name in ['code/canonical_checker.py', 'code/canonical_separate.py',
             'raw_scalar/checker.py', 'raw_scalar/control_separate.py',
             'raw_scalar/reference_ce5.py', 'reference/incoming_name_checker.py']:
    result['programs'][name] = measure(root / name)
(root / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
