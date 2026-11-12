"""Reproduce the delivered Python evidence; no Lean build is claimed."""
from pathlib import Path
import ast
import gzip
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def run(folder, script):
    result = subprocess.run([sys.executable, script], cwd=ROOT/folder, capture_output=True, text=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise SystemExit(result.returncode)

run('direct', 'verify.py')
run('strict', 'reproduce.py')
direct = json.loads((ROOT/'direct/verification.json').read_text())
strict = json.loads((ROOT/'strict/validation.json').read_text())
metrics = json.loads((ROOT/'strict/metrics.json').read_text())
normalized = ROOT/'evidence/normalized'
normalized.mkdir(exist_ok=True)
for name in ['native_checker.py', 'one_context_checker.py']:
    source = (ROOT/'direct'/name).read_text()
    data = (ast.unparse(ast.parse(source))+'\n').encode()
    (normalized/name).write_bytes(data)
    (normalized/(name+'.gz')).write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
receipt = {
    'python': sys.version,
    'direct': {k:v for k,v in direct.items() if k != 'outcomes'},
    'strict_validation_receipt': 'strict/validation.json',
    'strict_metrics': metrics,
    'lean_status': 'Not compiled: Lean and Lake were unavailable.',
    'mathematical_status': 'Written proofs and independent audits; finite executable regressions.'
}
(ROOT/'evidence/reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'direct_cli_checks':direct['cli_checks'], 'direct_mismatches':direct['mismatches'],
                  'substitution_checks':direct['semantic_substitution_checks'],
                  'strict_receipt':'strict/validation.json', 'status':'PASS',
                  'lean':'uncompiled'}, indent=2))
