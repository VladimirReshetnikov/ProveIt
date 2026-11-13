"""Reproduce source measurements, canonical compilation, and adversarial checks."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(relative_path):
    completed = subprocess.run([sys.executable, str(ROOT / relative_path)],
                               cwd=ROOT, text=True, capture_output=True)
    if completed.returncode:
        print(completed.stdout)
        print(completed.stderr, file=sys.stderr)
        raise SystemExit(completed.returncode)


def main():
    # Files modified by verification receipts are intentionally not hash-frozen.
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for item in manifest['files']:
        p = ROOT / item['path']
        if hashlib.sha256(p.read_bytes()).hexdigest() != item['sha256']:
            raise SystemExit('Archive file changed: ' + item['path'])
    run('code/measure.py')
    run('code/verify_candidates.py')
    run('diagnostics/test_nested_template.py')
    v = json.loads((ROOT / 'evidence/verification.json').read_text())
    n = json.loads((ROOT / 'diagnostics/nested_template_receipt.json').read_text())
    receipt = {
        'python': sys.version,
        'manifest_files_checked': len(manifest['files']),
        'checker_and_capture_processes': v['process_runs'],
        'nested_sort_control_processes': len(n['results']),
        'total_processes': v['process_runs'] + len(n['results']),
        'failures': v['failures'],
        'new_strict_envelope': [302, 340, 584],
        'one_program_below_old_strict_envelope': False,
        'compact_frontier_beaten': False,
    }
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
