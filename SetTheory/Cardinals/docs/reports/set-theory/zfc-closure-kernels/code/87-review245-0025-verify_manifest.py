"""Verify every sealed distribution file using explicit checks, not assertions."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parent.parent


def main():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = (ROOT / relative).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            raise ValueError('Missing or unsafe manifest entry: ' + relative)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError('SHA-256 mismatch: ' + relative)
        count += 1
    print(f'PASS: {count} sealed distribution files match their SHA-256 values')


if __name__ == '__main__':
    main()
