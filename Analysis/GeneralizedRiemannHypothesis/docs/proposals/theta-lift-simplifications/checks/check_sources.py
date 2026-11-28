"""Check the pinned source hashes and lines using a local ProveIt checkout."""
import argparse
import csv
import hashlib
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('checkout', type=Path, help='root of the ProveIt checkout')
args = parser.parse_args()
checked = {}
count = 0
with Path(__file__).with_name('sources.tsv').open(encoding='utf-8') as f:
    for row in csv.DictReader(f, delimiter='\t'):
        path = row['repository_path']
        if path not in checked:
            data = (args.checkout / path).read_bytes()
            header = b'blob ' + str(len(data)).encode() + b'\0'
            digest = hashlib.sha1(header + data).hexdigest()
            if digest != row['git_blob_sha1']:
                raise ValueError(f'Source version differs at {path}')
            checked[path] = data.decode('utf-8').splitlines()
        source_line = checked[path][int(row['line']) - 1]
        if hashlib.sha256(source_line.encode('utf-8')).hexdigest() != row['line_sha256']:
            raise ValueError(f'Anchor differs at {path}, line {row["line"]}')
        count += 1
print(f'PASS  {count} source anchors in {len(checked)} Git blobs')
