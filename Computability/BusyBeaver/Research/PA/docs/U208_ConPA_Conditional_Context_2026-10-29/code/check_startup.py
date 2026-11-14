#!/usr/bin/env python3
"""Independent complete 48,140-step blank startup and canonical endpoint."""
from pathlib import Path
import argparse
import hashlib
import json
from check_local import need, read_table

ROOT = Path(__file__).resolve().parents[1]


def execute(table, ticks):
    q, head, ones = 0, 0, set()
    visited, digest = set(), hashlib.sha256()
    for step in range(ticks):
        need(q != 254, 'Premature halt')
        bit = int(head in ones)
        w, d, target = table[q, bit]
        digest.update(f'{step} {q} {head} {bit} {w} {d} {target}\n'.encode())
        visited.add((q, bit))
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + d
    return (q, head, ones), digest.hexdigest(), visited


def check(output):
    old = read_table(ROOT / 'machine_parent/u209.native.tm')
    new = read_table(ROOT / 'machine/u208.native.tm')
    a, hash_a, visited = execute(old, 48140)
    b, hash_b, _ = execute(new, 48140)
    need(a == b and hash_a == hash_b, 'Startup trajectory changed')
    need(hash_a == '41e9a165abae389c3b182ebbf8d8fd1c260d3d36d4f7ebb6d60e235bac40f19a',
         'Wrong pinned startup trajectory')
    changed = {key for key in old if old[key] != new.get(key)}
    need(not changed & visited, 'Changed startup row visited')
    sites = json.loads((ROOT / 'machine/sites.json').read_text())
    need(sites == json.loads((ROOT / 'machine_parent/sites.json').read_text()),
         'Source changed')
    pc = sites[136][0]
    need(pc == '001100110101010' and a[:2] == (84, -2), 'Wrong entry frame')
    logical = [1, 0, 13, 0, 0, 1, 0, 0, 1]
    physical = [0] * 9
    for index, physical_index in enumerate((6, 2, 0, 4, 3, 7, 8, 5, 1)):
        physical[physical_index] = logical[index]
    expected = {-3, 54} | {-2 + i for i, bit in enumerate(pc) if bit == '1'}
    cursor = 55
    for value in physical + [1] * 43:
        expected.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    need(a[2] == expected and len(expected) == 120, 'Complete tape differs')
    result = {'status': 'EXACT_BLANK_STARTUP_PASS', 'steps': 48140,
              'endpoint_state_native': 84, 'head': -2, 'source_ordinal': 136,
              'source_address': pc, 'logical_registers': logical,
              'spares': [1] * 43, 'ones': sorted(expected),
              'header_distance': 56, 'zero_exterior': True,
              'trace_sha256': hash_a, 'changed_row_visits': 0}
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    print('EXACT_BLANK_STARTUP_PASS: 48140 steps, complete trace and tape equal')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    check(parser.parse_args().output)
