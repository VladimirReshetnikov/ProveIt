"""Check the distributed inventory and reproduce all executable evidence."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def verify_manifest():
    path = ROOT / 'MANIFEST.json'
    if not path.exists():
        return 0
    entries = json.loads(path.read_text())['files']
    for entry in entries:
        content = (ROOT / entry['path']).read_bytes()
        if len(content) != entry['bytes'] or hashlib.sha256(content).hexdigest() != entry['sha256']:
            raise ValueError('Changed distributed file: ' + entry['path'])
    return len(entries)


def main():
    count = verify_manifest()
    for script in ('code/measure_complete_sources.py', 'code/verify_kernels.py'):
        run = subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT,
                             capture_output=True, text=True)
        if run.returncode:
            raise SystemExit(run.stdout + run.stderr)
    metrics = json.loads((ROOT / 'evidence/final_metrics.json').read_text())
    tests = json.loads((ROOT / 'code/verification.json').read_text())
    print(json.dumps({
        'status': 'PASS', 'manifest_files_checked': count,
        'baseline_envelope': metrics['old_coordinatewise_envelope'],
        'new_envelope': metrics['new_separate_profile_envelope'],
        'single_program_below_all_baseline_minima': metrics['any_single_profile_below_all_old_coordinates'],
        'positive_certificates': tests['positive_certificates'],
        'negative_certificates': tests['negative_certificates'],
        'public_cli_checks': tests['public_cli_checks'],
        'mutated_packets': tests['mutated_packets'],
        'accepted_mutations_replayed_by_reference': tests['accepted_mutations_replayed_by_old_kernel'],
        'failures': tests['failures'],
    }, indent=2))


if __name__ == '__main__':
    main()
