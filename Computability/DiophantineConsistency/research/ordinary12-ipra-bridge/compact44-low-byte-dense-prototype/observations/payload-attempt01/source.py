#!/usr/bin/env python3
"""External parent-MC dense-region comparison; not a Lean file theorem."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

root = Path(__file__).resolve().parents[5]
p = root / ('Computability/DiophantineConsistency/candidates/'
            'free-j-polarized-positive/source/positive/coefficients/payloads/MC.bin.gz')
gz = p.read_bytes()
raw = gzip.decompress(gz)
h = lambda b: sha256(b).hexdigest()

def expected(j):
    r = (8*j) % 67
    return 254 if r == 0 else 255 - 2**(67-r) if r >= 60 else 255

miss = [j for j in range(17, 7890) if raw[j] != expected(j)]
checks = {
    'gzip_pin': h(gz) == '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    'raw_pin': h(raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'payload_unchanged': p.read_bytes() == gz,
    'length': len(raw),
    'length_matches': len(raw) == 73759,
    'start': 17,
    'end_exclusive': 7890,
    'window_count': 7890-17,
    'mismatch_count': len(miss),
    'all_windows_match': not miss,
}
print(json.dumps(checks, sort_keys=True, indent=2))
if not all(v for v in checks.values() if isinstance(v, bool)):
    raise SystemExit(1)
