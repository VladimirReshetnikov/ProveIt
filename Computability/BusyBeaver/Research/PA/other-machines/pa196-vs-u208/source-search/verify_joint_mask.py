#!/usr/bin/env python3
"""Compute and audit a joint zero/positive invariant for the PA196 source."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from collections import defaultdict, deque
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def successors(row, mask):
    """Sound transitions: bit j is 1 iff register j is strictly positive."""
    op = row[0]
    if op == 'halt':
        return ()
    if op == 'jump':
        return ((row[1], mask),)
    if op == 'inc':
        return ((row[2], mask | (1 << row[1])),)
    if op == 'dec':
        bit = 1 << row[1]
        if mask & bit:
            # A positive register becomes either zero or remains positive.
            return ((row[3], mask & ~bit), (row[3], mask))
        return ((row[2], mask),)
    raise ValueError(f'unknown operation {op}')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    # These modules pin the exact source trie and the three seed-definition files.
    rotations = load('pa196_rotations', HERE / 'scan_rotations.py')
    zero = load('pa196_zero_transfer', HERE / 'verify_zero_transfer.py')
    for rel, expected in zero.PINS.items():
        digest = hashlib.sha256((zero.UPSTREAM / rel).read_bytes()).hexdigest()
        require(digest == expected, f'changed upstream seed source: {rel}: {digest}')
    graph = rotations.graph(rotations.root)
    other_graph, _ = zero.interval_graph(rotations, rotations.root)
    require(graph == other_graph, 'independent source resolvers disagree')
    require(len(graph) == 3812 and all(None not in row for row in graph),
            'unexpected site count or source exit')
    initial = (25, 1)  # (2,0,0,0,0,0,0,0,0) has exactly bit 0 set.
    seen = {initial}
    work = deque([initial])
    while work:
        pc, mask = work.popleft()
        for successor in successors(graph[pc], mask):
            require(successor[0] is not None, 'unexpected source exit')
            if successor not in seen:
                seen.add(successor)
                work.append(successor)
    # Explicitly audit initial inclusion and closure after fixed-point discovery.
    require(initial in seen, 'initial state missing')
    for pc, mask in seen:
        require(all(s in seen for s in successors(graph[pc], mask)),
                f'invariant not closed at {(pc, mask)}')
    masks = defaultdict(set)
    for pc, mask in seen:
        masks[pc].add(mask)
    unreachable = [pc for pc in range(len(graph)) if not masks.get(pc)]
    forced_zero = []
    forced_positive = []
    for pc, row in enumerate(graph):
        if row[0] != 'dec' or not masks.get(pc):
            continue
        bit = 1 << row[1]
        if all(not (v & bit) for v in masks[pc]):
            forced_zero.append({'site': pc, 'register': row[1], 'masks': sorted(masks[pc])})
        if all(v & bit for v in masks[pc]):
            forced_positive.append({'site': pc, 'register': row[1], 'mask_count': len(masks[pc])})
    require(unreachable == [3774, 3775], 'abstract unreachable-site inventory changed')
    require([x['site'] for x in forced_zero] == [3773], 'forced-zero inventory changed')
    canonical = json.dumps(sorted(seen), separators=(',', ':')).encode()
    output = {'program_sha256': hashlib.sha256((zero.UPSTREAM / 'PA196/Program.lean').read_bytes()).hexdigest(),
              'seed_file_sha256': zero.PINS, 'seed_site': 25,
              'initial_register_vector': [2, 0, 0, 0, 0, 0, 0, 0, 0],
              'initial_mask': 1, 'registers': 9, 'source_sites': len(graph),
              'reachable_site_mask_pairs': len(seen), 'reachable_sites': len(masks),
              'unreachable_sites': unreachable, 'forced_zero_decrements': forced_zero,
              'forced_positive_decrement_count': len(forced_positive),
              'invariant_sha256': hashlib.sha256(canonical).hexdigest(),
              'independent_source_resolvers_agree': True,
              'initial_inclusion_and_all_successors_checked': True}
    out = json.dumps(output, indent=2, sort_keys=True) + '\n'
    print(out, end='')
    if args.output:
        args.output.write_text(out)


if __name__ == '__main__':
    main()
