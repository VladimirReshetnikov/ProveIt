#!/usr/bin/env python3
"""Check the unchanged source and whole blank startup, including exact trace."""
import argparse
import hashlib
import json
from pathlib import Path
from build import ROOT, read, census, need
import source_language as L
from source_interface import source_info, prefix_binding


def run(table, count):
    state = head = 0
    ones, used = set(), set()
    digest = hashlib.sha256()
    for tick in range(count):
        need(state != 254, 'Premature halt')
        b = int(head in ones)
        w, d, z = table[state, b]
        digest.update(f'{tick} {state} {head} {b} {w} {d} {z}\n'.encode())
        used.add((state, b))
        ones.add(head) if w else ones.discard(head)
        state, head = z, head + d
    return (state, head, ones), digest.hexdigest(), used


def check(machine, output):
    old = read(ROOT / 'baseline/u209.native.tm')
    new = read(Path(machine) / 'u208.native.tm')
    census(old, 209, 254)
    census(new, 208, 254)
    raw = (Path(machine) / 'sites.json').read_bytes()
    need(raw == (ROOT / 'baseline/sites.json').read_bytes(), 'Source changed')
    sites = json.loads(raw)
    branch, boundary, graph, metrics = source_info(sites)
    need(L.graph_intervals(sites) == L.graph_arithmetic(sites)[0], 'CFG resolvers')
    before, max_old = prefix_binding(old, branch)
    after, max_new = prefix_binding(new, branch)
    need(all(after[p] == (211 if q == 172 else q) for p, q in before.items()),
         'Prefix correspondence')
    a, ah, used = run(old, 48140)
    b, bh, _ = run(new, 48140)
    need(a == b and ah == bh, 'Startup differs')
    need(a[:2] == (84, -2), 'Startup dispatcher')
    registers = [1, 0, 13, 0, 0, 1, 0, 0, 1]
    physical = [0] * 9
    for i, j in enumerate((6, 2, 0, 4, 3, 7, 8, 5, 1)):
        physical[j] = registers[i]
    need(sites[136][0] == '001100110101010', 'Startup source site')
    expected = {-3, 54} | {-2 + i for i, bit in enumerate(sites[136][0]) if bit == '1'}
    position = 55
    for value in physical + [1] * 43:
        expected.update(range(position + 1, position + value + 2))
        position += value + 2
    need(a[2] == expected and len(expected) == 120, 'Whole canonical startup frame')
    delta = {key for key in set(old) | set(new) if old.get(key) != new.get(key)}
    need(not delta & used, 'Changed row visited before startup endpoint')
    result = {'status': 'SOURCE_AND_STARTUP_PASS', 'source_metrics': metrics,
              'source_sha256': hashlib.sha256(raw).hexdigest(),
              'source_primitives': len(sites), 'control_arrows': sum(len(x[2]) for x in graph),
              'internal_prefixes': len(branch), 'prefix_steps': [max_old, max_new],
              'startup_steps': 48140, 'startup_state': 84, 'startup_head': -2,
              'source_ordinal': 136, 'logical_registers': registers, 'spare_registers': [1] * 43,
              'one_cells': sorted(expected), 'complete_zero_exterior': True,
              'entire_startup_trace_equal': True, 'trace_sha256': ah,
              'changed_startup_rows': 0}
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--machine', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.machine, a.output), indent=2))
