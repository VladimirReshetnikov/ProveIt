#!/usr/bin/env python3
"""Check selected retained K bytes externally; this does not read a Lean proof."""
import gzip
import hashlib
import json
from pathlib import Path
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
root = next(p for p in Path(__file__).resolve().parents if (p / 'Computability').is_dir())
source = root / 'Computability/DiophantineConsistency/candidates/ten-positive-shifted-strong/coefficients/K.bin.gz'
compressed = source.read_bytes()
assert hashlib.sha256(compressed).hexdigest() == 'b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a'
raw = gzip.decompress(compressed)
assert len(raw) == 74111
assert hashlib.sha256(raw).hexdigest() == 'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e'
assert all(b == 0 for b in raw[18442:27613])
assert all(b == 0 for b in raw[46029:74110])
assert raw[74110] == 8
print(json.dumps({'status': 'PASS_EXTERNAL_INTERVAL_CHECK', 'raw_bytes': len(raw),
    'middle_zero_range_half_open': [18442, 27613],
    'trailing_zero_range_half_open': [46029, 74110], 'last_byte': 8,
    'scope': 'external gzip and file read; not a Lean file or decompression theorem'}, sort_keys=True))
