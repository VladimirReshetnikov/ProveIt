#!/usr/bin/env python3
"""Check the exact source rows outside the new AX emitter.

This is a finite CFG transplantation check, not an arithmetic semantic proof.
The old MP success entry is redirected to the retained copy-D routine, skipping
only the old dummy-zero push.  The new Shift prefix is two already proved
primitive routines: clear T, then copy H to T.  Every checked target is included.
"""
import argparse
import hashlib
import json
from pathlib import Path


def check(primary, candidate):
    old = json.loads(primary.read_text())
    new = json.loads(candidate.read_text())
    assert len(old) == 3673 and len(new) == 3671

    def targetmap(t):
        if t in (3661, 3671, 3672):
            return t - 2 if t >= 3671 else 3660
        if 3554 <= t <= 3634:
            return t + 18
        if 3653 <= t <= 3660:
            return t - 1
        return t

    def translate(row):
        k = 2 if row[0] in ("inc", "dec") else 1
        return row[:k] + [targetmap(t) for t in row[k:]]

    checked = []
    pairs = ([(i, i) for i in range(50)]
             + [(i, i + 18) for i in range(3554, 3634)]
             + [(i, i - 1) for i in range(3653, 3661)]
             + [(i, i - 2) for i in (3671, 3672)])
    for i, j in pairs:
        assert translate(old[i]) == new[j], (i, j, old[i], new[j])
        checked.append([i, j])

    def normalize(rows, offset):
        ans = []
        for row in rows:
            k = 2 if row[0] in ("inc", "dec") else 1
            ans.append(row[:k] + [t - offset for t in row[k:]])
        return ans

    assert normalize(new[3660:3662], 3660) == normalize(old[3533:3535], 3533)
    assert normalize(new[3662:3669], 3662) == normalize(old[69:76], 69)
    return {
        "status": "PASS",
        "scope": "Exact resolved-row transplantation outside AX; arithmetic helper contracts are inherited separately.",
        "primary_instructions_sha256": hashlib.sha256(primary.read_bytes()).hexdigest(),
        "candidate_instructions_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
        "checked_transplanted_rows": len(checked),
        "primary_to_new_rows": checked,
        "dispatch_remapped": True,
        "new_MP_success_entry": 3652,
        "old_MP_success_dummy_push_interval_removed": [3634, 3653],
        "H_clearT_source_prototype": [3533, 3535],
        "H_copyH_source_prototype": [69, 76],
        "H_prefix_new": [3660, 3669],
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--primary", type=Path, required=True)
    ap.add_argument("--candidate", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert __debug__, "Run this checker without Python -O."
    receipt = check(args.primary, args.candidate)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "primary_to_new_rows"}, indent=2))
