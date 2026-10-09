"""Verify the delivered file bytes against manifest.json; no network required."""
import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root/'manifest.json').read_text())
    failures = []
    for row in manifest['files']:
        path = root/row['path']
        if not path.is_file():
            failures.append({'path':row['path'], 'error':'missing'})
            continue
        data = path.read_bytes()
        if len(data)!=row['bytes'] or hashlib.sha256(data).hexdigest()!=row['sha256']:
            failures.append({'path':row['path'], 'error':'content mismatch'})
    print(json.dumps({'verified_files':len(manifest['files']), 'failures':failures},indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
