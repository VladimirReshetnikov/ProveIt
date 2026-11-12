"""Verify the delivered manifest, checks, and measurements."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def main():
    manifest_path = ROOT / 'MANIFEST.json'
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        for row in manifest['files']:
            data = (ROOT / row['path']).read_bytes()
            if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
                raise RuntimeError('Manifest mismatch: ' + row['path'])
        print('Manifest: all ' + str(len(manifest['files'])) + ' files match.', flush=True)
    for script in ['code/verify.py','code/check_bounded_risks.py','code/measure_baselines.py']:
        subprocess.run([sys.executable,'-B',str(ROOT / script)],cwd=ROOT,check=True)
    print('All checks and measurements completed successfully.')

if __name__ == '__main__':
    main()

