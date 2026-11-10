#!/usr/bin/env python3
"""Read-only external check of beta's pinned gzip/raw bytes and byte pattern."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
seed = here.parent / 'nine-sharing-sign17-degree96-vdifference-candidate' / 'seed.json'
sha = lambda data: hashlib.sha256(data).hexdigest()
raw_seed = seed.read_bytes()
assert sha(raw_seed) == '0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
doc = json.loads(raw_seed)
binding = doc['coefficient_binding']
beta = binding['ports']['beta']
packed = (seed.parent / binding['path'] / beta['file']).read_bytes()
assert sha(packed) == beta['gzip_sha256']
raw = gzip.decompress(packed)
assert sha(raw) == beta['raw_sha256'] and len(raw) == beta['raw_bytes'] == 11815
assert raw == bytes([31]) + bytes([255]) * 11814
assert int.from_bytes(raw, 'big') == (2**47)**2011 - 1
print(json.dumps({'status': 'PASS_EXTERNAL_BETA_BYTES', 'seed_sha256': sha(raw_seed),
 'gzip_sha256': sha(packed), 'raw_sha256': sha(raw), 'raw_bytes': len(raw),
 'representation': 'big-endian 0x1f followed by 11814 0xff bytes',
 'scope': 'External Python check; no Lean theorem or gzip-in-Lean binding.'}, indent=2, sort_keys=True))
