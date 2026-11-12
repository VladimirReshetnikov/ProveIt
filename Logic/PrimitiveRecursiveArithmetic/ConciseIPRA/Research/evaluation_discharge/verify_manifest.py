"""Verify the SHA-256 ledger of the original delivered payload."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    ledger = json.loads((ROOT / 'MANIFEST.json').read_text())
    failures = []
    for record in ledger['files']:
        path = ROOT / record['path']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
            failures.append(record['path'])
    if failures:
        raise SystemExit('Changed or absent: ' + ', '.join(failures))
    print(f"VERIFIED {len(ledger['files'])} files")


if __name__ == '__main__':
    main()
