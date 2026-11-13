"""Verify the delivered files before running scripts that refresh receipts."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parent.parent

def main():
    failures = []
    lines = (ROOT / 'MANIFEST.sha256').read_text().splitlines()
    for line in lines:
        digest, name = line.split('  ', 1)
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            failures.append(name)
    if failures:
        raise SystemExit('Manifest mismatch: ' + ', '.join(failures))
    print(f'All {len(lines)} file hashes match the delivered manifest.')

if __name__ == '__main__':
    main()
