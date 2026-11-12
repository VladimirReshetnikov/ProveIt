"""Verify the delivered package and reproduce its concrete evidence offline."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    manifest_file = ROOT / 'MANIFEST.json'
    files_verified = 0
    if manifest_file.exists():
        manifest = json.loads(manifest_file.read_text())
        for entry in manifest['files']:
            p = ROOT / entry['path']
            if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != entry['sha256']:
                raise RuntimeError('Payload hash mismatch: ' + entry['path'])
            files_verified += 1
        print('Original payload manifest: PASS')
    operations = []
    for script in ['code/measure_sources.py', 'code/validate_kernels.py',
                   'code/validate_scalar_supports.py']:
        run = subprocess.run([sys.executable, script], cwd=ROOT,
                             capture_output=True, text=True)
        operations.append({'script': script, 'returncode': run.returncode})
        if run.returncode:
            print(run.stdout[-6000:])
            print(run.stderr[-6000:])
            raise SystemExit(run.returncode)
        print(script + ': PASS')
    receipt = {'status': 'PASS', 'original_manifest_present': manifest_file.exists(),
               'payload_files_verified': files_verified, 'operations': operations,
               'scope': 'Package hashes and finite executable evidence; written metatheory is not proof-assistant verified'}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
