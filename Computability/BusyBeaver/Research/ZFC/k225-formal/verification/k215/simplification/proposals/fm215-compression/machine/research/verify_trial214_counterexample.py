#!/usr/bin/env python3
"""Reject one tempting 214-state fold by a concrete valid runtime frame.

This is a counterexample to the uniform primitive-runtime contract, not a
claim about the trial's blank run or consistency equivalence. No external
dependencies or inherited checker execution are required.
"""
from pathlib import Path
import hashlib
import json
import argparse
if not __debug__:
    raise RuntimeError('This checker requires assertions; do not run Python with -O.')

ROOT = Path(__file__).resolve().parent.parent
PARENT_SHA = "da83e8de52f4d9536cee2d5ed4af4311308bda51196d18891b96e4bc9ca6cb4f"
TRIAL_SHA = "c160b744c578ed29a493133a276669e5df56b9df6961bc29150c114de115bef7"
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SITE = ["1101001000", "CD", 3]

def read_table(file):
    raw = file.read_bytes()
    table = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, z = line.split()
        table[int(q), int(b)] = int(w), 1 if d == "R" else -1, int(z)
    return raw, table

def frame(pc, logical, spares, gap=0):
    physical = [None] * 9
    for i, j in enumerate(PHY):
        physical[j] = logical[i]
    ones = {-1, 64 + gap} | {i for i, b in enumerate(pc) if b == "1"}
    pos = 65 + gap
    for value in physical + list(spares):
        pos += 1
        ones.update(range(pos, pos + value + 1))
        pos += value + 1
    return ones

def clean_dispatch(q, h, ones):
    if q != 84 or h - 1 not in ones or any(x < h - 1 for x in ones):
        return False
    right = sorted(x for x in ones if x >= h + 52)
    if not right or right[0] < h + 64:
        return False
    pos, last, values = right[0] + 1, max(ones), []
    while pos < last:
        if pos in ones or pos + 1 not in ones:
            return False
        start = pos + 1
        pos = start
        while pos in ones:
            pos += 1
        values.append(pos - start - 1)
    return pos == last + 1 and len(values) >= 10

def run(table, initial, limit=100000):
    q, h, ones = 84, 0, set(initial)
    for tick in range(limit + 1):
        if tick and (clean_dispatch(q, h, ones) or (q, int(h in ones)) not in table):
            return (q, h, ones), tick
        if tick == limit:
            raise AssertionError("runtime bound exhausted")
        w, d, z = table[q, int(h in ones)]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        q, h = z, h + d
    raise AssertionError("unreachable")

def describe(conf):
    q, h, ones = conf
    return {"state": q, "head": h, "ones": sorted(ones)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'research/trial214_counterexample.json')
    args = parser.parse_args()
    source = (ROOT / 'research/commands120.sites215.json').read_bytes()
    assert hashlib.sha256(source).hexdigest() == 'd5c994e3d0c8fe26dd337aca48e5f25ff4f28fd18973f2c04c99589d6ba3f53d'
    assert json.loads(source)[25] == SITE
    raw, parent = read_table(ROOT / "tables/01.tm")
    trial_raw, trial = read_table(ROOT / "research/trial214.native.tm")
    assert hashlib.sha256(raw).hexdigest() == PARENT_SHA
    assert hashlib.sha256(trial_raw).hexdigest() == TRIAL_SHA
    assert parent[78, 0] == (0, 1, 26)
    assert parent[210, 0] == (0, 1, 201)
    assert parent[78, 1] == parent[210, 1] == (0, -1, 302)
    expected_trial = {(q, b): (w, d, 78 if z == 210 else z)
                      for (q, b), (w, d, z) in parent.items() if q != 210}
    expected_trial[78, 0] = (0, 1, 201)
    assert trial == expected_trial
    assert len({q for q, _ in trial}) == 214
    registers, spares, gap = [0] * 9, [0], 0
    initial = frame(SITE[0], registers, spares, gap)
    # Zero CD3 removes the last zero from the address and increments its prefix.
    prefix = SITE[0][:SITE[0].rfind("0")]
    successor_pc = format(int(prefix, 2) + 1, "0" + str(len(prefix)) + "b")
    want = (84, 0, frame(successor_pc, registers, spares, gap))
    old, old_steps = run(parent, initial)
    actual, trial_steps = run(trial, initial)
    assert old == want and actual != want
    assert clean_dispatch(*actual) and old_steps == 610 and trial_steps == 594
    assert want[2] - actual[2] == {8} and actual[2] - want[2] == {11}
    record = {
        "status": "CONCRETE_RUNTIME_CONTRACT_COUNTEREXAMPLE",
        "scope": "Valid runtime-frame counterexample, not a blank-run claim",
        "parent_sha256": PARENT_SHA, "trial_sha256": TRIAL_SHA,
        "source_site_ordinal_zero_based": 25, "site": SITE,
        "logical_registers": registers, "spares": spares, "gap": gap,
        "initial": describe((84, 0, initial)), "expected_pc": successor_pc,
        "parent_steps": old_steps, "trial_steps": trial_steps,
        "expected": describe(want), "parent_actual": describe(old),
        "trial_actual": describe(actual), "trial_clean_dispatch": True,
        "missing_one_cells": [8], "extra_one_cells": [11],
        "checked_parent_matches": True,
        "representation": "Native controls; dispatcher 84, halt 254"
    }
    output = args.output
    output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in
          ("status", "scope", "parent_steps", "trial_steps",
           "missing_one_cells", "extra_one_cells")}, indent=2))

if __name__ == "__main__":
    main()

