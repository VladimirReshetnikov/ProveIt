#!/usr/bin/env python3
"""Match the paper's source anchors to Git blob identities in a readable grh/ checkout."""
import argparse
import csv
from hashlib import sha1
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('grh', type=Path, help='readable package directory containing src/')
    args = parser.parse_args()
    manifest = Path(__file__).resolve().parents[1] / 'source-anchors.tsv'
    files = {}
    with manifest.open(encoding='utf-8', newline='') as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    for row in rows:
        path = args.grh / row['file_in_grh']
        if path not in files:
            raw = path.read_bytes()
            digest = sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            files[path] = (digest, raw.decode('utf-8').splitlines())
        digest, lines = files[path]
        n = int(row['line'])
        if digest != row['git_blob_sha1'] or not 1 <= n <= len(lines) or row['source_anchor'] not in lines[n - 1]:
            raise SystemExit(f'Source mismatch at {path}:{n}')
    print(f'Verified {len(rows)} source anchors in {len(files)} distinct Git blobs.')


if __name__ == '__main__':
    main()
