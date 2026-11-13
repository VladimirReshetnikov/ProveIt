"""Reproduce the delivered checks without modifying the extracted archive."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    manifest = ROOT / 'MANIFEST.sha256'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            path = ROOT / name
            if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise SystemExit('Manifest mismatch: ' + name)
    clean_env = dict(os.environ)
    clean_env.pop('PYTHONOPTIMIZE', None)
    clean_env.pop('PYTHONPATH', None)
    outputs = {}
    with tempfile.TemporaryDirectory(prefix='ipra-export-reproduction-') as directory:
        work = Path(directory)
        for package in ('newest_use', 'compact476'):
            shutil.copytree(ROOT / package, work / package,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            result = subprocess.run([sys.executable, '-B', str(work / package / 'verify.py')],
                                    cwd=work / package, env=clean_env,
                                    text=True, capture_output=True, timeout=180)
            if result.returncode:
                raise SystemExit(package + ' failed:\n' + result.stdout + result.stderr)
            outputs[package] = json.loads(result.stdout)
        shutil.copy2(ROOT / 'proof_node_audit.py', work / 'proof_node_audit.py')
        result = subprocess.run([sys.executable, '-B', str(work / 'proof_node_audit.py')],
                                cwd=work, env=clean_env, text=True,
                                capture_output=True, timeout=60)
        if result.returncode:
            raise SystemExit('Proof-node audit failed:\n' + result.stderr)
        outputs['proof_node_audit'] = json.loads(result.stdout)
    print(json.dumps({'python': sys.version, 'verified': True, 'results': outputs}, indent=2))


if __name__ == '__main__':
    main()
