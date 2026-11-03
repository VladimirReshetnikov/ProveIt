#!/usr/bin/env python3
"""Externally check a fixed parent-MC payload prefix, not a Lean theorem."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

root = Path(__file__).resolve().parents[5]
p = root / ('Computability/DiophantineConsistency/candidates/'
            'free-j-polarized-positive/source/positive/coefficients/payloads/MC.bin.gz')
compressed = p.read_bytes()
raw = gzip.decompress(compressed)
h = lambda x: sha256(x).hexdigest()
checks = {
    'gzip_pin': h(compressed) == '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    'raw_pin': h(raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'payload_unchanged': compressed == p.read_bytes(),
    'raw_length': len(raw),
    'prefix_hex': raw[:16].hex(),
    'prefix_matches': raw[:16] == bytes([254] + [255]*15),
}
print(json.dumps(checks, sort_keys=True, indent=2))
if not all(v for v in checks.values() if isinstance(v, bool)):
    raise SystemExit(1)
