#!/usr/bin/env python3
"""Recompute source metrics from the pinned Git commit and bundled replacements."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

bundle = Path(__file__).resolve().parents[1]
repository = Path(sys.argv[1] if len(sys.argv) > 1 else '.').resolve()
manifest = json.loads((bundle / 'validation/manifest.json').read_text())
results = []
for item in manifest['files']:
    old = subprocess.run(
        ['git', '-C', str(repository), 'show', manifest['base_commit'] + ':' + item['path']],
        check=True, stdout=subprocess.PIPE).stdout
    new = (bundle / 'replacements' / item['path']).read_bytes()
    for data, field in [(old, 'before_sha256'), (new, 'after_sha256')]:
        if hashlib.sha256(data).hexdigest() != item[field]:
            raise SystemExit('Hash mismatch: ' + item['path'] + ' / ' + field)
    before, after = len(old.splitlines()), len(new.splitlines())
    if (before, after) != (item['before_lines'], item['after_lines']):
        raise SystemExit('Line count mismatch: ' + item['path'])
    results.append({'file': item['path'], 'before': before, 'after': after,
                    'net_removed': before - after})
print(json.dumps({'files': results, 'total_net_removed': sum(x['net_removed'] for x in results)}, indent=2))
