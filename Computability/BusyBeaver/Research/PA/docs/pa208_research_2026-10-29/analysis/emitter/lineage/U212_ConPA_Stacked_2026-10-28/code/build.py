#!/usr/bin/env python3
"""Deterministic two-row construction and dense relabeling of U212."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT_SHA = 'bb4f5ac12b29d07d1080109af9bb564e9e11a4783efc48cd73b8f826789d01f7'
NATIVE_SHA = '386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4'
DENSE_SHA = 'c979e55e6a6f75b08effdf67067cceb460e30a4c28aef9c79797d0a6d32a074e'
SOURCE_SHA = '7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00'

def need(condition, message):
    if not condition:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def parse(raw):
    table, starts = {}, []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        need(q >= 0 and target >= 0 and b in (0, 1) and w in (0, 1), 'row domain')
        need(direction in ('L', 'R') and (q, b) not in table, 'bad or duplicate row')
        table[q, b] = w, 1 if direction == 'R' else -1, target
    need(starts == [0], 'start label must be 0')
    return table

def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {target}\n'
        for (q, b), (w, d, target) in sorted(table.items()))).encode('ascii')

def validate(table, count, halt):
    states = {q for q, _ in table}
    need(len(states) == count, 'working-state count')
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, 'incomplete table')
    need(0 in states and halt not in states, 'start/halt census')
    need({target for _, _, target in table.values()} - states == {halt}, 'target closure')
    seen, pending = {0}, [0]
    for q in pending:
        for bit in (0, 1):
            target = table[q, bit][2]
            if target != halt and target not in seen:
                seen.add(target)
                pending.append(target)
    need(seen == states, 'graph-unreachable working state')
    return states

def construct(parent_path, output):
    raw = Path(parent_path).read_bytes()
    need(digest(raw) == PARENT_SHA, 'wrong literal parent')
    parent = parse(raw)
    validate(parent, 213, 254)
    need(parent[180, 1] == (1, 1, 172), 'old bypass row')
    need(parent[172, 0] == (0, -1, 112), 'old fold row')
    intermediate = dict(parent)
    intermediate[180, 1] = 1, 1, 211
    child = {key: act for key, act in intermediate.items() if key[0] != 112}
    child[172, 0] = 0, -1, 67
    states = validate(child, 212, 254)
    native = encode(child)
    need(digest(native) == NATIVE_SHA, 'native identity')
    rename = {q: i for i, q in enumerate(sorted(states))}
    rename[254] = 212
    inverse = {i: q for q, i in rename.items()}
    need(len(inverse) == 213 and rename[0] == 0, 'renaming bijection')
    dense_table = {(rename[q], b): (w, d, rename[target])
                   for (q, b), (w, d, target) in child.items()}
    validate(dense_table, 212, 212)
    dense = encode(dense_table)
    need(digest(dense) == DENSE_SHA, 'dense identity')
    need({(inverse[q], b): (w, d, inverse[target])
          for (q, b), (w, d, target) in dense_table.items()} == child,
         'inverse relabeling differs')
    mapping = {'native_to_dense': rename, 'dense_to_native': inverse,
               'start': 0, 'native_halt': 254, 'dense_halt': 212}
    summary = {'status': 'EXACT_U212_RECONSTRUCTION_PASS', 'working_states': 212,
               'transition_rows': 424, 'start': 0, 'dense_halt': 212,
               'native_halt': 254, 'symbols': [0, 1], 'tapes': 1,
               'moves': ['L', 'R'], 'initial_tape': 'all zeros',
               'graph_reachable_states': 212, 'deleted_native_state': 112,
               'changed_native_rows': [[180, 1, 1, 1, 211], [172, 0, 0, -1, 67]],
               'native_sha256': NATIVE_SHA, 'dense_sha256': DENSE_SHA,
               'parent_native_sha256': PARENT_SHA, 'source_sha256': SOURCE_SHA}
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    for name, data in [('u212.native.tm', native), ('u212.tm', dense),
                       ('stage1.native.tm', encode(intermediate))]:
        (output / name).write_bytes(data)
    for name, data in [('state_map.json', mapping), ('summary.json', summary)]:
        (output / name).write_text(json.dumps(data, indent=2) + '\n')
    return summary

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent', type=Path, default=ROOT / 'inputs/parent213.native.tm')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(construct(args.parent, args.output), indent=2))
