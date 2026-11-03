#!/usr/bin/env python3
"""External parent-MC gap observations and precise disjoint-coverage count."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

root = Path(__file__).resolve().parents[5]
p = root / ('Computability/DiophantineConsistency/candidates/'
            'free-j-polarized-positive/source/positive/coefficients/payloads/MC.bin.gz')
gz = p.read_bytes()
raw = gzip.decompress(gz)
gaps = [(7898,8225), (8317,8392), (8643,8895), (8920,9163),
        (9179,18375), (18392,27596)]
existing = [(0,16), (17,7890), (27613,73751)]
all_intervals = sorted(existing + gaps)
disjoint = all(all_intervals[i][1] <= all_intervals[i+1][0]
               for i in range(len(all_intervals)-1))
uncovered = []
cursor = 0
for lo, hi in all_intervals:
    if cursor < lo:
        uncovered.append([cursor, lo])
    cursor = hi
if cursor < len(raw):
    uncovered.append([cursor, len(raw)])
h = lambda b: sha256(b).hexdigest()
checks = {
    'gzip_pin': h(gz) == '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    'raw_pin': h(raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'payload_unchanged': p.read_bytes() == gz,
    'length_matches': len(raw) == 73759,
    'six_gaps': gaps,
    'six_gaps_count': sum(hi-lo for lo,hi in gaps),
    'all_gap_bytes_255': all(v == 255 for lo,hi in gaps for v in raw[lo:hi]),
    'all_intervals_disjoint': disjoint,
    'covered_count': sum(hi-lo for lo,hi in all_intervals),
    'uncovered': uncovered,
    'uncovered_count': sum(hi-lo for lo,hi in uncovered),
}
print(json.dumps(checks, sort_keys=True, indent=2))
if not all(v for v in checks.values() if isinstance(v, bool)):
    raise SystemExit(1)
