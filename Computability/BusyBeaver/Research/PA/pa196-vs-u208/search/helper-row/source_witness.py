#!/usr/bin/env python3
"""Replay a valid source-frame counterexample to the PA196 helper fold."""
import argparse
from collections import deque
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PA = HERE.parents[2]
SOURCE = PA / 'pa196-vs-u208/source-search'
TABLE = PA / 'jamesyc-upstream/pa196/data/pa196.tm'
TABLE_HASH = 'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def frame(path, file, extra):
    """Head at 0, left marker at -1, gap marker at 48 + extra."""
    need(len(path) <= 48 and extra >= 0, 'invalid path or gap')
    marker = 48 + extra
    ones = {-1, marker} | {i for i, bit in enumerate(path) if bit}
    pos = marker + 1
    for value in file:
        need(value >= 0, 'negative register')
        ones.update(range(pos + 1, pos + value + 2))
        pos += value + 2
    return ones


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    need(hashlib.sha256(TABLE.read_bytes()).hexdigest() == TABLE_HASH, 'table hash differs')
    rows = {}
    for line in TABLE.read_text().splitlines():
        q, read, write, direction, dst = line.split()
        key = int(q), int(read)
        need(key not in rows and direction in ('L', 'R'), 'bad literal table')
        rows[key] = int(write), (-1 if direction == 'L' else 1), int(dst)
    need(len(rows) == 392 and rows[184, 1] == (1, 1, 78), 'unexpected table')
    rotations = load('pa196_source_rotations', SOURCE / 'scan_rotations.py')
    joint = load('pa196_source_joint', SOURCE / 'verify_joint_mask.py')
    zero = load('pa196_source_zero', SOURCE / 'verify_zero_transfer.py')
    for rel, digest in zero.PINS.items():
        need(hashlib.sha256((zero.UPSTREAM / rel).read_bytes()).hexdigest() == digest,
             f'seed input changed: {rel}')
    paths = list(rotations.leaf_occurrences(rotations.root))
    graph = rotations.graph(rotations.root)
    other_graph, _ = zero.interval_graph(rotations, rotations.root)
    need(graph == other_graph and len(paths) == 3812, 'source graph mismatch')
    need(graph[604] == ('dec', 2, 612, 605), 'site operation mismatch')
    # Independent audit of the existing finite, jointly tracked sign abstraction.
    initial = (25, 1)
    seen = {initial}
    work = deque([initial])
    while work:
        pc, mask = work.popleft()
        for state in joint.successors(graph[pc], mask):
            need(state[0] is not None, 'source exits unexpectedly')
            if state not in seen:
                seen.add(state)
                work.append(state)
    need(all(all(s in seen for s in joint.successors(graph[pc], mask))
             for pc, mask in seen), 'joint invariant is not closed')
    masks604 = sorted(mask for pc, mask in seen if pc == 604)
    need(len(masks604) == 112 and 7 in masks604, 'site 604 mask inventory changed')
    # From PhysicalRegisters.lean, logical r maps to the following physical slot.
    permutation = [6, 2, 0, 4, 3, 7, 8, 5, 1]
    initial_file = [1, 0, 1, 0, 0, 0, 1, 0, 0] + [1] * 26
    logical_mask = sum((initial_file[permutation[i]] > 0) << i for i in range(9))
    need(logical_mask == 7, 'frame is not admitted by site/mask abstraction')
    orig_file = [0, 0, 1, 0, 0, 0, 1, 0, 0] + [1] * 26
    child_file = [1, 0, 1, 0, 0, 0, 1, 0, 1] + [1] * 27
    start = frame(paths[604][0], initial_file, 0)
    orig_target = frame(paths[605][0], orig_file, 1)
    child_target = frame(paths[615][0], child_file, 0)
    records = []
    for candidate, horizon, target in ((False, 414, orig_target), (True, 664, child_target)):
        ones = set(start)
        q, head = 75, 0
        hits = []
        parent_target_seen = []
        trace = []
        for step in range(horizon + 1):
            if (q, head, ones) == (75, 0, orig_target):
                parent_target_seen.append(step)
            if q in (160, 184, 185, 187):
                mask = sum((int(head + i in ones) << (i + 2)) for i in range(-2, 3))
                hits.append([step, q, head, int(head in ones), mask])
            trace.append([q, head, sorted(ones)])
            if step == horizon:
                break
            need(q != 196, 'unexpected early halt')
            read = int(head in ones)
            write, direction, dst = rows[q, read]
            if candidate and (q, read) == (184, 1):
                write, direction, dst = 1, -1, 75
            if candidate and dst == 45:
                dst = 160
            ones.discard(head)
            if write:
                ones.add(head)
            head += direction
            q = dst
        need((q, head, ones) == (75, 0, target), 'exact final configuration mismatch')
        if candidate:
            need(not parent_target_seen, 'candidate reaches parent endpoint within horizon')
        else:
            need(parent_target_seen == [414], 'unexpected parent target steps')
        need([31, 184, 27, 1, 6] in hits, 'adverse context mismatch')
        encoded = json.dumps(trace, separators=(',', ':')).encode()
        records.append({'candidate': candidate, 'steps': horizon,
                        'final_site': 615 if candidate else 605,
                        'final_head': head, 'final_state': q,
                        'final_file': child_file if candidate else orig_file,
                        'final_marker_position': 48 if candidate else 49,
                        'final_one_cells': sorted(ones),
                        'parent_exact_target_seen_at': parent_target_seen,
                        'affected_state_visits': hits,
                        'full_trace_sha256': hashlib.sha256(encoded).hexdigest()})
    output = {'table_sha256': TABLE_HASH,
              'program_sha256': hashlib.sha256((zero.UPSTREAM / 'PA196/Program.lean').read_bytes()).hexdigest(),
              'joint_invariant_size': len(seen), 'site_604_admitted_mask_count': len(masks604),
              'initial_logical_mask': logical_mask,
              'initial_site': 604,
              'paths': {str(i): ''.join(map(str, paths[i][0])) for i in (604, 605, 615)},
              'initial_file': initial_file, 'initial_marker_position': 48,
              'initial_one_cells': sorted(start), 'runs': records}
    out = json.dumps(output, sort_keys=True, indent=2) + '\n'
    print(out, end='')
    if args.output:
        args.output.write_text(out)


if __name__ == '__main__':
    main()
