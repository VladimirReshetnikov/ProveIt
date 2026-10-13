#!/usr/bin/env python3
"""Replay delivered example packets without modifying the evidence files."""
from pathlib import Path
import json, sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cycleblocks import verify_plan, verify_power_certificate, transport_circuit
from cycleblocks.__main__ import integer_keys
from tests.oracles import spanning_forests, brute_private

p = json.loads((ROOT/'results/binary_cycle_2pow1024.json').read_text())
assert verify_power_certificate(p['certificate'])
assert p['certificate']['parameters']['length'] == 1 << 1025
valid = [e['score'] for e in p['certificate']['table']
         if e['first'] + e['last'] <= 1 and e['direction'] == 0]
assert max(valid) == p['matched_weight'] == (1 << 1024)-1
assert p['deferred_weight'] == 1

w = json.loads((ROOT/'examples/weighted_cactus.json').read_text())
plan = json.loads((ROOT/'examples/weighted_cactus_plan.json').read_text())
counts, weights = integer_keys(w['counts'], True), integer_keys(w['weights'])
assert verify_plan(counts, plan, weights)
assert plan['matched_weight'] == brute_private(counts, weights) == 18
assert plan['transport'] == transport_circuit(counts, plan, weights)

f = json.loads((ROOT/'examples/forest_choice_witness.json').read_text())
counts, weights = integer_keys(f['counts'], True), integer_keys(f['weights'])
edges = integer_keys(f['edges'])
assert verify_plan(counts, f['plan'], weights)
actual = {tuple(sorted(tree)) for tree in spanning_forests(4, edges)}
assert tuple(sorted(f['forest']['forest'])) in actual
assert set(f['forest']['forest']).isdisjoint(c for _, c in f['plan']['cancellations'])
for row in f['forest_scores']:
    tree = tuple(sorted(row['forest']))
    assert tree in actual
    a = {r: {c: x for c, x in values.items() if c not in tree} for r, values in counts.items()}
    assert brute_private(a, weights) == row['score']
assert max(x['score'] for x in f['forest_scores']) == f['plan']['matched_weight'] == 4
print('PASS: binary complete-table proof, exact cycle score, weighted plan/transport, and all 16 forest scores')
