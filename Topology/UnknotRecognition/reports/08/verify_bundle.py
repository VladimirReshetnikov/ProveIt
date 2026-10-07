"""Verify the payload hashes and the exact pinned baseline Git blobs."""
from pathlib import Path
import hashlib
import json


def main():
    root = Path(__file__).resolve().parent
    count = 0
    listed = set()
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        relative = Path(name)
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError(f'Invalid manifest path: {name}')
        data = (root / relative).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f'SHA-256 mismatch: {name}')
        listed.add(name)
        count += 1
    expected = {str(path.relative_to(root)) for path in root.rglob('*')
                if path.is_file() and path.name != 'SHA256SUMS'
                and '__pycache__' not in path.parts and path.suffix not in {'.pyc', '.pyo'}}
    if listed != expected:
        raise ValueError(f'Manifest coverage differs: {sorted(listed ^ expected)}')
    provenance = json.loads((root / 'PROVENANCE.json').read_text())
    prefix = 'Topology/UnknotRecognition/fast/'
    for record in provenance['baseline_files']:
        if not record['path'].startswith(prefix):
            raise ValueError('Unexpected baseline path')
        path = root / 'baseline/fast' / record['path'][len(prefix):]
        data = path.read_bytes()
        git_hash = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if git_hash != record['sha']:
            raise ValueError(f'Baseline Git blob mismatch: {path}')
    print(f'OK: {count} SHA-256 payload hashes and '
          f'{len(provenance["baseline_files"])} pinned baseline Git blobs.')


if __name__ == '__main__':
    main()
