#!/usr/bin/env python3
"""Verify target bytes in a ProveIt checkout against the reviewed manifest."""
from pathlib import Path
import argparse
import hashlib
import json

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('repository', type=Path)
args = parser.parse_args()
manifest = json.loads((root / 'evidence' / 'source_targets.json').read_text())
failures = []
for entry in manifest['files']:
    path = args.repository / entry['path']
    actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    if actual != entry['sha256']:
        failures.append({'path': entry['path'], 'actual': actual, 'expected': entry['sha256']})
print(json.dumps({'snapshot': manifest['snapshot'], 'files_checked': len(manifest['files']),
                  'all_passed': not failures, 'failures': failures}, indent=2))
raise SystemExit(1 if failures else 0)
