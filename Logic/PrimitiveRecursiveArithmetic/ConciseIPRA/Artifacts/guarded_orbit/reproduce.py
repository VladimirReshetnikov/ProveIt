"""Regenerate proof certificates, verification receipts and source metrics."""
from pathlib import Path
import gzip
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
subprocess.run([sys.executable, str(ROOT / 'tests/build_proofs.py')], cwd=ROOT, check=True)
run = subprocess.run([sys.executable, str(ROOT / 'measure.py')], cwd=ROOT,
                     check=True, capture_output=True, text=True)
rows = json.loads(run.stdout)
(ROOT / 'evidence/metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
for row in rows:
    path = ROOT / row['path']
    if row['path'].startswith('code/'):
        path.with_suffix(path.suffix + '.gz').write_bytes(
            gzip.compress(path.read_bytes(), compresslevel=9, mtime=0))
controls = []
for name, expected in [('old_atomic_case_rejected', True), ('retired_mode_toggle', False)]:
    data = (ROOT / 'tests/certificates' / (name + '_local.json')).read_bytes()
    for optimized in (False, True):
        cmd = [sys.executable] + (['-O'] if optimized else []) + [
            str(ROOT / 'reference/source_dispatch_checker_bytes.py')]
        run = subprocess.run(cmd, input=data, capture_output=True, timeout=20)
        accepted = run.returncode == 0 and run.stdout == b'ACCEPT\n'
        controls.append({'case': name, 'optimized': optimized, 'expected': expected,
                         'accepted': accepted, 'matched': accepted == expected,
                         'returncode': run.returncode})
receipt = {'runs': len(controls), 'matches': sum(r['matched'] for r in controls),
           'results': controls}
(ROOT / 'evidence/matched_baseline_controls.json').write_text(json.dumps(receipt, indent=2) + '\n')
if receipt['matches'] != receipt['runs']:
    raise SystemExit('Matched predecessor control failed')
summary = json.loads((ROOT / 'evidence/validation.json').read_text())
print(json.dumps({'checks': summary['runs'] + receipt['runs'],
                  'matches': summary['matches'] + receipt['matches'],
                  'mismatches': len(summary['mismatches']),
                  'compact_profiles': [r for r in rows if r['path'] in (
                      'code/checker.py', 'code/checker_bytes.py', 'code/checker_tokens.py')]}, indent=2))
