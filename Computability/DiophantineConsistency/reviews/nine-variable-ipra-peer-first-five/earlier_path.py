#!/usr/bin/env python3
"""Compare the earlier warning-rejected stage-2 object with accepted author."""
from hashlib import sha256
import json
from pathlib import Path
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
E = Path('/tmp/nine-ipra-guarded-author-20261102-e/attempts/002-001')
H = Path('/tmp/nine-ipra-guarded-author-20261102-h')
f = json.loads((E / 'failure.json').read_text())
r = json.loads((H / 'receipts/002.json').read_text())
x = (E / 'object.olean').read_bytes()
y = Path(r['output']['resolved']).read_bytes()
p, q = f['command'][5].encode(), r['command'][5].encode()
assert f['stage'] == 'compile' and f['exit'] == 0 and f['object_present']
assert len(x) == len(y) and len(p) == len(q) and x.count(p) == y.count(q) == 1
assert x.find(p) == y.find(q) == 1008328 and x.replace(p, q) == y
different = [i for i, (a, b) in enumerate(zip(x, y)) if a != b]
assert different == [1008367]
print(json.dumps({'status': 'EARLY_WARNING_OBJECT_DIFFERS_ONLY_IN_SOURCE_PATH',
                  'earlier_sha256': sha256(x).hexdigest(),
                  'author_sha256': sha256(y).hexdigest(),
                  'differing_byte_offsets': different,
                  'path_offset': x.find(p), 'path_length': len(p),
                  'scope': 'byte comparison only; earlier attempt lacked retained direct-input guards'},
                 indent=2, sort_keys=True))
