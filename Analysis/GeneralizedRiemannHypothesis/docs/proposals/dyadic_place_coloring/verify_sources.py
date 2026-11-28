#!/usr/bin/env python3
"""Verify inspected Git blob identifiers against a checkout. No network calls."""
import csv
import hashlib
from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit('Usage: python3 verify_sources.py /path/to/ProveIt')
root = Path(sys.argv[1])
audit = Path(__file__).with_name('source_audit.tsv')
failures = []
with audit.open(encoding='utf-8', newline='') as f:
    records = list(csv.DictReader(f, delimiter='\t'))
for record in records:
    path = root / record['repo_path']
    try:
        data = path.read_bytes()
    except OSError as exc:
        failures.append(f'{path}: {exc}')
        continue
    blob = hashlib.sha1(f'blob {len(data)}\0'.encode('ascii') + data).hexdigest()
    if blob != record['git_blob_sha1']:
        failures.append(f'{path}: expected {record["git_blob_sha1"]}, got {blob}')
for problem in failures:
    print(problem, file=sys.stderr)
print(f'{len(records)-len(failures)}/{len(records)} source blobs match.')
raise SystemExit(bool(failures))
