#!/usr/bin/env python3
"""Compare central radius-5 projections of radius-6 reachable windows."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'sources/proveit/Computability/BusyBeaver/Research/ZFC'))
import audit_tm

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('table', type=Path)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
data = args.table.read_bytes()
assert hashlib.sha256(data).hexdigest() == '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
machine = audit_tm.parse_table(data.decode())
start = time.monotonic()
w5 = audit_tm.window_reachable(machine, 5)
w6 = audit_tm.window_reachable(machine, 6)
removed = {}
for state, windows in w5.items():
    projected = {(value >> 1) & 2047 for value in w6.get(state, [])}
    assert projected <= set(windows)
    difference = set(windows) - projected
    if difference:
        removed[state] = len(difference)
result = {'radius5_configurations': sum(map(len, w5.values())),
          'radius6_configurations': sum(map(len, w6.values())),
          'removed_radius5_patterns': sum(removed.values()),
          'states_tightened': removed,
          'elapsed_seconds': time.monotonic() - start}
assert result['radius5_configurations'] == 102061
assert result['radius6_configurations'] == 335369
assert result['removed_radius5_patterns'] == 1604 and len(removed) == 33
args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({k:v for k,v in result.items() if k != 'states_tightened'}))
