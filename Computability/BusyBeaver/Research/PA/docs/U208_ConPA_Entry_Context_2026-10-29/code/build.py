#!/usr/bin/env python3
"""Rebuild the exact U208 tables from sealed U209 tables; no search."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT = 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'
EXPECTED = {
    'u208.native.tm': 'b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135',
    'u208.tm': 'a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1',
    'u208_compatibility.native.tm':
        '5f936da0cf393548cdd1eeebcaf7490d7a42f4ccca115f865a7bcc045463eb52',
    'u208_compatibility.tm':
        '9865dcd7bd44deece098c16dcec7b90a96cf111592cbd37e3531b50f7b09276c',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    table = {}
    starts = []
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line.split()[-1]))
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        need((q, bit) not in table, 'Duplicate row')
        need(bit in (0, 1) and write in (0, 1) and direction in ('L', 'R'), 'Alphabet')
        table[q, bit] = write, 1 if direction == 'R' else -1, target
    need(starts == [0], 'Initial state')
    return table


def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(table.items()))).encode('ascii')


def census(table, count, halt):
    states = {q for q, _ in table}
    need(0 in states and halt not in states and len(states) == count, 'State count')
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Complete table')
    need({z for w, d, z in table.values()} - states == {halt}, 'Halt convention')
    seen, queue = {0}, [0]
    for q in queue:
        for b in (0, 1):
            z = table[q, b][2]
            if z != halt and z not in seen:
                seen.add(z)
                queue.append(z)
    need(seen == states, 'Unreachable working state in transition graph')
    return sorted(states)


def build(output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    need(hashlib.sha256((ROOT / 'baseline/u209.native.tm').read_bytes()).hexdigest()
         == PARENT, 'Parent identity')
    records = {}
    for stem, path, helper in [
        ('u208', ROOT / 'baseline/u209.native.tm', 217),
        ('u208_compatibility', ROOT / 'comparison/compatibility/u209.native.tm', 214),
    ]:
        old = read(path)
        census(old, 209, 254)
        new = {(q, b): (w, d, 211 if z == 172 else z)
               for (q, b), (w, d, z) in old.items() if q != 172}
        new[211, 0] = 0, -1, helper
        states = census(new, 208, 254)
        mapping = {q: i for i, q in enumerate(states)}
        mapping[254] = 208
        dense = {(mapping[q], b): (w, d, mapping[z])
                 for (q, b), (w, d, z) in new.items()}
        census(dense, 208, 208)
        for suffix, table in [('.native.tm', new), ('.tm', dense)]:
            name, raw = stem + suffix, encode(table)
            need(hashlib.sha256(raw).hexdigest() == EXPECTED[name], 'Exact bytes: ' + name)
            (output / name).write_bytes(raw)
        if stem == 'u208':
            state_map = {'native_to_dense': mapping,
                         'dense_to_native': {v: k for k, v in mapping.items()},
                         'native_halt': 254, 'dense_halt': 208}
            (output / 'state_map.json').write_bytes(
                (json.dumps(state_map, indent=2) + '\n').encode('utf-8'))
        records[stem] = {'working_states': 208, 'transitions': 416,
                         'helper': helper, 'graph_reachable': 208}
    (output / 'sites.json').write_bytes((ROOT / 'baseline/sites.json').read_bytes())
    result = {'status': 'EXACT_BUILD_PASS', 'machines': records, 'sha256': EXPECTED}
    (output / 'build.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    print(json.dumps(build(p.parse_args().output), indent=2))
