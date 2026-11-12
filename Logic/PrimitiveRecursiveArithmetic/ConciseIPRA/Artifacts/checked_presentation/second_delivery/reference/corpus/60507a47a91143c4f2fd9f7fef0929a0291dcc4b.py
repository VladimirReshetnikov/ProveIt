"""Verify the delivered payload against its SHA-256 manifest."""
import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    failures = []
    for relative, expected in manifest['sha256'].items():
        path = root / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(relative)
    if failures:
        raise SystemExit('Changed or missing files: ' + ', '.join(failures))
    print('Verified', len(manifest['sha256']), 'delivered payload files.')


if __name__ == '__main__':
    main()
