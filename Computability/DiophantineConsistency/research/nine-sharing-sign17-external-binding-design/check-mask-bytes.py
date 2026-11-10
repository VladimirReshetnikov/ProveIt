#!/usr/bin/env python3
"""External re-computation of the two masks and comparison to frozen bytes."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
seed = here.parent / 'nine-sharing-sign17-degree96-vdifference-candidate' / 'seed.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
text = seed.read_bytes()
assert sha(text) == '0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
binding = json.loads(text)['coefficient_binding']
radix = 2**47
beta = radix**2011 - 1
support = set(range(951)) | set(range(960, 986)) | {1004}
assert len(support) == 978
low = beta - sum(radix**j for j in support)
prefix = [4] + [8]*916 + [0]*43 + [1]*9 + [0]*18 + [1]*8 + [0]*9 + [1, 2**45-4]
digits = prefix + [0]*1005
assert len(prefix) == 1006 and len(digits) == 2011
high = 0
for digit in reversed(digits):
    high = high * radix + digit
expected = {'MC': low, 'MF': high + beta}
results = {}
for name, value in expected.items():
    record = binding['ports'][name]
    packed = (seed.parent / binding['path'] / record['file']).read_bytes()
    raw = gzip.decompress(packed)
    assert sha(packed) == record['gzip_sha256'] and sha(raw) == record['raw_sha256']
    assert len(raw) == record['raw_bytes'] and int.from_bytes(raw, 'big') == value
    results[name] = {'gzip_sha256': sha(packed), 'raw_sha256': sha(raw), 'raw_bytes': len(raw)}
print(json.dumps({'status':'PASS_EXTERNAL_MASK_RECOMPUTATION', 'seed_sha256':sha(text),
    'ports':results, 'scope':'External Python recomputation of formulas; not a Lean theorem or file binding.'}, indent=2, sort_keys=True))
