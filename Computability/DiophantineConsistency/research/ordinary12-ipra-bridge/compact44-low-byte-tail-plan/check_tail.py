#!/usr/bin/env python3
"""Observe the retained parent MC all-one tail; not a Lean certificate."""
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
checks = {
    'gzip_pin': h(gz) == '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    'raw_pin': h(raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'payload_unchanged': p.read_bytes() == gz,
    'length': len(raw),
    'length_matches': len(raw) == 73759,
    'tail_start_inclusive': 27605,
    'tail_end_exclusive': 73758,
    'tail_bytes_all_255': all(v == 255 for v in raw[27605:73758]),
    'top_byte_is_31': raw[73758] == 31,
}
print(json.dumps(checks, sort_keys=True, indent=2))
if not all(v for v in checks.values() if isinstance(v, bool)):
    raise SystemExit(1)
