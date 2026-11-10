"""Check every distributed member against its SHA-256 and exact byte size."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    manifest = json.loads((ROOT / 'MANIFEST.sha256.json').read_text())
    failures = []
    for row in manifest['files']:
        path = ROOT / row['path']
        if not path.is_file():
            failures.append({'path': row['path'], 'error': 'missing'})
            continue
        data = path.read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            failures.append({'path': row['path'], 'error': 'content differs'})
    print(json.dumps({'checked_files': len(manifest['files']), 'failures': failures}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
