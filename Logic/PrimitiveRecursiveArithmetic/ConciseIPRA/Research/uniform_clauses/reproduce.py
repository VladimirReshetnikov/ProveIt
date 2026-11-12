"""Reproduce the proof checks and report the complete-checker measurements."""
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
work = root / 'validation'
evidence = root / 'evidence'
evidence.mkdir(exist_ok=True)
if (root / 'code/checker.py').read_bytes() != (work / 'clausal_horn_shared.py').read_bytes():
    raise SystemExit('The delivered checker differs from the validated copy.')
result = subprocess.run([sys.executable, str(work / 'verify.py')],
                        cwd=work, text=True, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT)
(evidence / 'reproduction_log.txt').write_text(result.stdout)
if result.returncode:
    print(result.stdout)
    raise SystemExit(result.returncode)
summary = json.loads((work / 'evidence/results.json').read_text())
(evidence / 'validation_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
normalized = (work / 'evidence/clausal_horn_shared.normalized.py').read_bytes()
if normalized != (root / 'code/checker_normalized.py').read_bytes():
    raise SystemExit('Normalized checker differs; inspect the Python version.')
print('PASS: {} positive certificates; {} adversarial certificates; '
      '{} malformed documents; {} full process checks.'.format(
          summary['positive_theorems'], summary['adversarial_certificates'],
          summary['malformed_documents'], summary['public_process_checks']))
for row in summary['metrics']:
    print('{program}: {normalized_bytes} bytes, {significant_tokens} tokens, '
          '{ast_nodes} AST nodes, {gzip9_bytes} gzip bytes'.format(**row))
