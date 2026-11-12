"""Check the manifest, then regenerate implementation evidence."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    manifest = ROOT / 'SHA256SUMS'
    if manifest.exists():
        checked = 0
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
                raise RuntimeError('Hash mismatch: ' + name)
            checked += 1
        print('Verified file hashes:', checked, flush=True)
    for script in ['verify.py', 'measure.py', 'scope_completion_audit.py']:
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'code' / script)],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        if result.returncode:
            raise RuntimeError(script + '\n' + result.stdout + result.stderr)
        output = json.loads(result.stdout)
        (ROOT / 'evidence' / (script[:-3] + '.json')).write_text(
            json.dumps(output, indent=2) + '\n')
        print(script + ': passed', flush=True)
    metrics = json.loads((ROOT / 'code/measurements.json').read_text())['programs'][0]
    assert (metrics['normalized_bytes'], metrics['significant_tokens'],
            metrics['ast_nodes']) == (1925, 630, 701)
    print('Selected complete-module metrics: 1925 bytes, 630 tokens, 701 AST nodes.')
    print('General metatheorems are written proofs; the finite checks do not formalize them.')


if __name__ == '__main__':
    main()
