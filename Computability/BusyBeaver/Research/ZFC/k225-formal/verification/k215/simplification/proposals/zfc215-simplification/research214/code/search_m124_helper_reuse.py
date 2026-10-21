#!/usr/bin/env python3
"""Bounded exact local helper-reuse search; no global lower-bound claim.

Searches replacement rows for marker215 state124/read0 after deleting helper127.
Unknown external tape cells are branched on, and every branch must return to
the exact mapped old endpoint with the complete visited tape restored.
The checked-in positive sanity case is the existing three-step helper block.
"""
if not __debug__: raise RuntimeError('Run with assertions enabled, without -O.')
from pathlib import Path
import argparse
import json
import time

HERE = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument('--table', type=Path, default=HERE/'marker215_packet/candidate/marker215.native.tm')
ap.add_argument('--output', type=Path, default=HERE/'final_helper_reuse_search.json')
args = ap.parse_args()
table = {}
for line in args.table.read_text().splitlines():
    if not line or line.startswith('#'):
        continue
    q, b, w, d, z = line.split()
    table[int(q), int(b)] = int(w), 1 if d == 'R' else -1, int(z)

states = sorted({q for q, b in table} - {127})
assert len(states) == 214
stats = {}
hits = []
nodes = 0

def prove(entry, marker, write, move, allow127=False):
    global nodes
    goal = 14 if marker == 0 else 62
    stack = [(entry, move, {-1: marker, 0: write}, {-1: marker, 0: 0}, 0)]
    explored = 0
    while stack:
        q, h, tape, original, step = stack.pop()
        explored += 1
        nodes += 1
        if explored > 4096:
            return 'branch_cap'
        if q == goal and h == 1 and tape == original:
            continue
        if step >= 96:
            return 'step_cap'
        if (q == 127 and not allow127) or (q, 0) not in table:
            return 'halt_or_missing'
        if h not in tape:
            if len(tape) >= 10:
                return 'cell_cap'
            for bit in (0, 1):
                new_tape, new_original = tape.copy(), original.copy()
                new_tape[h] = new_original[h] = bit
                stack.append((q, h, new_tape, new_original, step))
            continue
        bit = tape[h]
        w, d, z = table[q, bit]
        if q == 124 and bit == 0:
            w, d, z = write, move, entry
        new_tape = tape.copy()
        new_tape[h] = w
        stack.append((z, h+d, new_tape, original, step+1))
    return 'PASS'

assert prove(127, 0, 0, -1, allow127=True) == 'PASS'
assert prove(127, 1, 0, -1, allow127=True) == 'PASS'
nodes = 0
start = time.monotonic()
for write, move in [(0, -1), (0, 1), (1, -1), (1, 1)]:
    for entry in states:
        first = prove(entry, 0, write, move)
        stats[first] = stats.get(first, 0) + 1
        if first == 'PASS':
            second = prove(entry, 1, write, move)
            key = 'second_' + second
            stats[key] = stats.get(key, 0) + 1
            if second == 'PASS':
                hits.append({'entry': entry, 'write': write, 'move': move})

result = {
    'elapsed': time.monotonic() - start,
    'candidates_tested': 856,
    'table_sha256': __import__('hashlib').sha256(args.table.read_bytes()).hexdigest(),
    'removed_state': 127, 'modified_row': [124,0],
    'hits': hits,
    'stats': stats,
    'symbolic_nodes': nodes,
    'existing_helper_positive_sanity_case': 'PASS',
    'bounds': {'transitions_after_first': 96, 'visited_cells': 10, 'nodes_per_case': 4096},
    'scope': 'Exact endpoint14/62 with head+1 and whole tape restored, arbitrary outside tape. No result within bounded class; bound exits do not imply impossible reuse.'
}
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
