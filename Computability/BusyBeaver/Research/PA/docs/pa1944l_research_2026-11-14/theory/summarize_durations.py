#!/usr/bin/env python3
"""Check the affine clock bounds used by the relative iPRA proof."""
import hashlib
import json
from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: python3 summarize_durations.py PATH/TO/contracts.json")
raw = Path(sys.argv[1]).read_bytes()
contracts = json.loads(raw)
durations = [row["duration"] for row in contracts]
assert len(durations) == 4780
assert all(len(d) == 13 and all(isinstance(x, int) and x >= 0 for x in d) for d in durations)
assert all(d[0] >= 3 for d in durations)
bound = [534, 8] + [4] * 9 + [2, 2]
assert all(all(a <= b for a, b in zip(d, bound)) for d in durations)
result = {
    "contracts_sha256": hashlib.sha256(raw).hexdigest(),
    "outcomes": len(contracts),
    "minimum_constant": min(d[0] for d in durations),
    "slotwise_maximum_coefficient": [max(d[i] for d in durations) for i in range(13)],
    "all_nonnegative": True,
    "max_sum_coefficients": max(map(sum, durations)),
    "uniform_upper_bound_coefficients": bound,
    "slot_order": ["constant", "gap"] + [f"register_{i}" for i in range(9)] + ["first_spare", "remaining_spare_list_width"],
}
print(json.dumps(result, indent=2))
