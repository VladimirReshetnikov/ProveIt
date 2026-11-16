#!/usr/bin/env python3
"""Check exact upstream Git blob identities and the standalone transformation."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'UPSTREAM_SOURCES.json').read_text())
kernel = (root / 'ObjectKernel.lean').read_text()
results = []
for item in manifest['sources']:
    raw = (root / item['local']).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert blob == item['git_blob_sha'], (item['path'], blob, item['git_blob_sha'])
    embedded_ok = None
    if item['embedded']:
        name = Path(item['local']).name
        start = '-- BEGIN UPSTREAM ' + name + '\n'
        end = '-- END UPSTREAM ' + name
        section = kernel.split(start, 1)[1].split(end, 1)[0].strip()
        expected = '\n'.join(line for line in raw.decode().split('\n')
                             if not line.startswith('import ')).strip()
        assert section == expected, name
        embedded_ok = True
    results.append({'path': item['path'], 'git_blob_sha': blob,
                    'original_bytes_match': True, 'embedded_body_match': embedded_ok})
print(json.dumps({'commit': manifest['commit'], 'status': 'passed', 'sources': results}, indent=2))
