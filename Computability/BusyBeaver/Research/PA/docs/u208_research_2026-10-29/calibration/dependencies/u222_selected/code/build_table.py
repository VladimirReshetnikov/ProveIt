#!/usr/bin/env python3
"""Reconstruct a literal table from a fixed patch, then relabel bijectively.

The baseline is the accepted ProveIt K215 machine. The data recipe was produced
by the corrected contextual allocator, but reproduction invokes no allocator
or solver. Exact transition correspondence of native and dense presentations
is checked on every row. Mathematical runtime and logic certificates are
separate from this finite reconstruction check.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def parse(raw):
    table = {}
    starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q, bit, write, direction, target = line.split()
            q, bit, write, target = map(int, (q, bit, write, target))
            require((q, bit) not in table, 'Duplicate transition')
            require(bit in (0, 1) and write in (0, 1) and direction in ('L', 'R'),
                    'Invalid transition')
            table[q, bit] = write, (-1 if direction == 'L' else 1), target
    require(starts == [0], 'The table must start in state 0')
    return table


def encode(table):
    return ('#! start 0\n'+''.join(
        f'{q} {bit} {write} {"R" if direction == 1 else "L"} {target}\n'
        for (q, bit), (write, direction, target) in sorted(table.items())
    )).encode('ascii')


def valid(table, halt):
    states = {q for q, _ in table}
    require(0 in states and halt not in states, 'Invalid start or halt state')
    require(set(table) == {(q, bit) for q in states for bit in (0, 1)},
            'Incomplete binary table')
    require(all(write in (0, 1) and direction in (-1, 1) and target in states | {halt}
                for write, direction, target in table.values()), 'Invalid target or action')
    reached = {0}
    todo = [0]
    for q in todo:
        for bit in (0, 1):
            target = table[q, bit][2]
            if target != halt and target not in reached:
                reached.add(target)
                todo.append(target)
    require(reached == states, 'Unreachable state in graph census')
    return states


def build(baseline, recipe):
    original = baseline.read_bytes()
    require(sha(original) == recipe['baseline_sha256'], 'Baseline hash mismatch')
    table = parse(original)
    changes = recipe['changed_rows']
    require(len({tuple(row[:2]) for row in changes}) == len(changes), 'Duplicate patch row')
    for q, bit, write, direction, target in changes:
        table[q, bit] = write, direction, target
    removed = set(recipe['removed_states'])
    table = {key: value for key, value in table.items() if key[0] not in removed}
    states = valid(table, 254)
    require(len(states) == recipe['states'], 'Working-state count mismatch')
    native = encode(table)
    require(sha(native) == recipe['native_sha256'], 'Native table hash mismatch')
    rename = {int(q): int(r) for q, r in recipe['native_to_dense'].items()}
    require(set(rename) == states | {254}, 'Incomplete renaming map')
    require(set(rename.values()) == set(range(len(states)+1)), 'Renaming is not bijective')
    require(rename[0] == 0 and rename[254] == len(states), 'Start/halt renaming mismatch')
    dense_table = {(rename[q], bit): (write, direction, rename[target])
                   for (q, bit), (write, direction, target) in table.items()}
    valid(dense_table, len(states))
    inverse = {r: q for q, r in rename.items()}
    require({(inverse[q], bit): (write, direction, inverse[target])
             for (q, bit), (write, direction, target) in dense_table.items()} == table,
            'Renaming does not preserve every literal transition')
    dense = encode(dense_table)
    require(sha(dense) == recipe['dense_sha256'], 'Dense table hash mismatch')
    return native, dense


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=here.parent/'inputs/k215.native.tm')
    parser.add_argument('--recipe', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    recipe = json.loads(args.recipe.read_text())
    native, dense = build(args.baseline, recipe)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output/'u.native.tm').write_bytes(native)
    (args.output/'u.tm').write_bytes(dense)
    mapping={'native_to_dense':recipe['native_to_dense'],
             'native_halt':254,'dense_halt':recipe['states'],'start':0}
    summary={'status': 'EXACT_TABLE_RECONSTRUCTION_AND_RELABELING_PASS',
             'working_states': recipe['states'], 'transitions': 2*recipe['states'],
             'native_sha256': sha(native), 'dense_sha256': sha(dense),
             'source_sha256':recipe['source_sha256']}
    (args.output/'state_map.json').write_text(json.dumps(mapping,indent=2)+'\n')
    (args.output/'machine_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
