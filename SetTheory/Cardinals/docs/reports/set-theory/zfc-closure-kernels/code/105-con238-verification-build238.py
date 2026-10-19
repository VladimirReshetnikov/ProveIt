#!/usr/bin/env python3
"""Construct and independently initialize the exact 238-state table.

The two input reductions are attributed in ATTRIBUTION.md. This script checks
their literal composition, the canonical state bijection, and the complete
blank prefix with independent sparse and dense tape representations. It does
not substitute finite execution for the separate unbounded runtime proof.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
BOUNDARY = ROOT / 'vendor/boundary239'
START, DISPATCH, HALT = 95, 96, 254
BOOT_STEPS = 409835
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
EXPECTED = {
    'boundary239': 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719',
    'rotation240': '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f',
    'delayed239': '76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b',
    'final_old': '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c',
    'final_canonical': '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08',
    'source': '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    result, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            require(start is None, 'Duplicate start declaration')
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, n = line.split()
            q, b, w, n = map(int, (q, b, w, n))
            require((q, b) not in result, 'Duplicate transition')
            require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Invalid action')
            result[q, b] = w, d, n
    return result, start


def encode(t, start):
    return ('#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {n}\n' for (q, b), (w, d, n) in sorted(t.items()))).encode()


def delayed(t):
    require(t[147, 0] == (0, 'R', 169), 'Unexpected caller')
    require(t[80, 0] == (0, 'R', 25), 'Unexpected reused state')
    require(t[91, 1] == (0, 'L', 50), 'Unexpected helper')
    require([k for k, v in t.items() if v[2] == 169] == [(147, 0)], 'Unexpected incoming edge')
    result = {k: v for k, v in t.items() if k[0] != 169}
    result[147, 0] = 0, 'R', 80
    result[80, 0] = 0, 'L', 106
    result[91, 1] = 1, 'L', 167
    return result


def changes(a, b):
    return [{'state': q, 'read': bit, 'old': a.get((q, bit)), 'new': b.get((q, bit))}
            for q, bit in sorted(a.keys() | b.keys()) if a.get((q, bit)) != b.get((q, bit))]


def sparse(t, start, count):
    q, h, ones = start, 0, set()
    visits = Counter()
    low = high = 0
    for _ in range(count):
        b = int(h in ones)
        require((q, b) in t, 'Premature halt in blank prefix')
        w, d, n = t[q, b]
        visits[q, b] += 1
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += 1 if d == 'R' else -1
        q = n
        low, high = min(low, h), max(high, h)
    return q, h, sorted(ones), visits, [low, high]


def dense(t, start, count):
    offset = count + 1
    cells = bytearray(2 * count + 3)
    position, q = offset, start
    for _ in range(count):
        w, move, q = t[q, cells[position]]
        cells[position] = w
        position += (move == 'R') - (move == 'L')
    return q, position - offset, [i - offset for i, b in enumerate(cells) if b]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Use Python with assertions enabled')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    paths = {
        'boundary239': BOUNDARY / 'candidate239/zfc_boundary239_old.tm',
        'rotation240': BOUNDARY / 'baseline/rotation240/zfc_rotation240_old.tm',
        'delayed239': ROOT / 'reference/delayed239_old.tm',
        'source': ROOT / 'source/sites_logical.json',
    }
    for name, path in paths.items():
        require(digest(path) == EXPECTED[name], f'Input hash mismatch: {name}')
    b, _ = table(paths['boundary239'])
    rotation, _ = table(paths['rotation240'])
    d, _ = table(paths['delayed239'])
    require(delayed(rotation) == d, 'Prior delayed construction mismatch')
    final = delayed(b)
    states = {q for q, bit in final}
    require(len(states) == 238 and len(final) == 476, 'Wrong state census')
    require(set(final) == {(q, bit) for q in states for bit in (0, 1)}, 'Non-total working table')
    require({v[2] for v in final.values()} - states == {HALT}, 'Wrong halt target')
    require(169 not in states and 218 not in states, 'Deleted state remains')
    order = [START] + sorted(states - {START})
    mapping = {q: i for i, q in enumerate(order)} | {HALT: 238}
    canonical = {(mapping[q], bit): (w, move, mapping[n])
                 for (q, bit), (w, move, n) in final.items()}
    old_path, canonical_path = out / 'zfc238_old.tm', out / 'zfc238.tm'
    old_path.write_bytes(encode(final, START))
    canonical_path.write_bytes(encode(canonical, 0))
    require(digest(old_path) == EXPECTED['final_old'], 'Final old-label hash mismatch')
    require(digest(canonical_path) == EXPECTED['final_canonical'], 'Canonical hash mismatch')
    reread, declared = table(canonical_path)
    require(reread == canonical and declared == 0, 'Canonical serialization mismatch')
    for key, value in final.items():
        q, bit = key
        w, move, n = value
        require(reread[mapping[q], bit] == (w, move, mapping[n]), 'Action bijection failed')
    reached, todo = set(), [START]
    while todo:
        q = todo.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != HALT:
            todo.extend(final[q, bit][2] for bit in (0, 1))
    require(reached == states | {HALT}, 'Unexpected unreachable graph state')

    a = sparse(final, START, BOOT_STEPS)
    require(a[:3] == dense(final, START, BOOT_STEPS), 'Sparse/dense disagreement')
    c = dense(canonical, 0, BOOT_STEPS)
    require(c == (mapping[a[0]], a[1], a[2]), 'Canonical blank execution disagrees')
    predecessor = sparse(b, START, 409691)
    require(a[:3] == predecessor[:3], 'Predecessor whole tape mismatch')
    q, head, one_positions = a[:3]
    require((q, head, len(one_positions)) == (DISPATCH, -5, 351), 'Wrong blank endpoint')
    ones = set(one_positions)
    require(min(ones) == head - 1, 'Wrong marker or nonzero left exterior')
    header = min(x for x in ones if x >= head)
    require(header == 176, 'Wrong header')
    position, values = header + 1, []
    while position <= max(ones):
        require(position not in ones and position + 1 in ones, 'Malformed unary block')
        first = position + 1
        position = first
        while position in ones:
            position += 1
        values.append(position - first - 1)
    logical = [values[i] for i in PHY]
    require(logical == [3, 0, 0, 0, 3, 0, 0, 0, 0], 'Wrong logical seed')
    require(values[9:] == [1] * 167, 'Wrong complete spare suffix')
    blank = {
        'status': 'EXACT_238_SPARSE_DENSE_CANONICAL_BOOT_PASS',
        'steps': BOOT_STEPS, 'initial_state': 0, 'initial_head': 0,
        'initial_tape': 'All zeros on the integers', 'final_state': mapping[DISPATCH],
        'final_state_old': DISPATCH, 'final_head': head, 'marker': head - 1,
        'header': header, 'header_distance': header - head, 'additional_gap': header - head - 64,
        'pc': '', 'physical_registers': values[:9], 'logical_registers': logical,
        'spare_values': values[9:], 'one_count': len(one_positions),
        'all_one_positions': one_positions, 'all_other_cells_zero': True,
        'head_range': a[4], 'agrees_with_boundary239_complete_configuration': True,
        'predecessor_steps': 409691, 'additional_steps': 144,
        'table_sha256': digest(old_path), 'canonical_table_sha256': digest(canonical_path),
    }
    result = {
        'status': 'EXACT_238_CONSTRUCTION_PASS', 'working_states': 238,
        'transition_rows': 476, 'separate_halt_state': 238, 'canonical_start': 0,
        'canonical_dispatcher': mapping[DISPATCH], 'deleted_inherited_states': [169, 218],
        'all_working_states_graph_reachable': True,
        'graph_reachability_scope': 'Graph only; no claim that the blank run visits every state.',
        'canonical_sha256': digest(canonical_path), 'inherited_sha256': digest(old_path),
        'source_sha256': digest(paths['source']), 'exact_blank_prefix_steps': BOOT_STEPS,
        'changes_from_boundary239': changes(b, final),
        'changes_from_rotation240': changes(rotation, final),
        'scope': 'Literal construction, totality, state bijection and complete finite initialization. '
                 'Source calibration and unbounded runtime are checked separately.',
    }
    for name, data in [('blank_prefix.json', blank), ('construction.json', result),
                       ('renumbering.json', mapping)]:
        (out / name).write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if not k.startswith('changes_')}, indent=2))


if __name__ == '__main__':
    main()
