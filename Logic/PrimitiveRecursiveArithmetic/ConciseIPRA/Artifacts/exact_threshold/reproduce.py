"""Measure the counted module and check the shipped standalone examples."""
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
CHECKER = ROOT/'code/checker.py'
source = CHECKER.read_text()
tree = ast.parse(source)
normalized = ast.unparse(tree)+'\n'
skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
metrics = {
    'python':sys.version,
    'source_sha256':hashlib.sha256(CHECKER.read_bytes()).hexdigest(),
    'tokens':sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
    'ast_nodes':len(list(ast.walk(tree))),
    'normalized_bytes':len(normalized.encode()),
}
failures = []
if tuple(metrics[k] for k in ('tokens','ast_nodes','normalized_bytes')) != (314,357,590):
    failures.append('Published metrics differ on this Python runtime')
results = []
for path in sorted((ROOT/'examples').glob('*.json')):
    expected = not path.name.startswith('reject_')
    for checker in (CHECKER,ROOT/'code/readable.py'):
        r = subprocess.run([sys.executable,str(checker)],input=path.read_text(),
                           text=True,capture_output=True,timeout=20)
        got = r.returncode == 0 and r.stdout == 'ACCEPT\n'
        results.append({'example':path.name,'checker':checker.name,'expected':expected,'accepted':got})
        if got != expected:failures.append(results[-1])
receipt = {'metrics':metrics,'standalone_runs':results,'failures':failures,
           'note':'Finite tests do not establish universal soundness; see the written proof.'}
(ROOT/'evidence/reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'metrics':metrics,'standalone_runs':len(results),'failures':failures},indent=2))
if failures:raise SystemExit(1)
