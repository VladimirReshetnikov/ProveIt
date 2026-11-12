"""Verify hashes of the original delivered payload before regeneration."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    failures = []
    for name, expected in manifest['sha256'].items():
        path = ROOT / name
        actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        if actual != expected:
            failures.append(name)
    if failures:
        raise SystemExit('Hash mismatch: ' + ', '.join(failures))
    print(f"Verified {len(manifest['sha256'])} delivered files")


if __name__ == '__main__':
    main()
