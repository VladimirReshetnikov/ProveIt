#!/usr/bin/env python3
"""Deterministically rebuild U210 and U209; no search, network, or optimizer.

The independently written check_u210/check_u209 modules and the universal
runtime checker discharge the semantic obligations separately.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import source_language as L

ROOT = Path(__file__).resolve().parents[1]
ROTATIONS_210 = ((162, 203, 0), (203, 223, 0), (223, 188, 0), (188, 177, 0),
                 (177, 89, 0), (89, 174, 0), (174, 217, 0), (217, 163, 0))
ROTATIONS_209 = ((206, 199, 1), (205, 206, 1), (7, 205, 1))
PARENT_TABLE = '7edae566b4c2e5c34d88030e0ae7caa49edda32c174b06b1a68bf9eb78567c8d'
PARENT_SOURCE = 'a1c81a3abff846a329a109927ce92d0be1553b7af2671855cdfe5bc4d6d953d1'
EXPECTED = {
    'u210.native.tm': '262032bf4237bd9c30e16ab7a3c2c4c50015a00c722ddf523e93cec0dbc51a37',
    'u210.tm': '9020e082ef6995d13cd571c325f4d83bf615f4d0a82e77c580353c1127a0d596',
    'u210.sites.json': 'a9693855883ba010144d9ac47f4c286e133b07301efb1b8379349824a2aa0669',
    'u209.native.tm': '4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1',
    'u209.tm': 'bda91bd40880f96edef104246d22797fe281355cf03610ab7e93e7923be8aa16',
    'u209.sites.json': '912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def parse(path):
    table, starts = {}, []
    for line in Path(path).read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line.split()[-1]))
        if not line or line.startswith('#'):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        need((q, b) not in table and b in (0, 1) and w in (0, 1), 'Row domain')
        need(d in ('L', 'R'), 'Direction')
        table[q, b] = (w, 1 if d == 'R' else -1, t)
    need(starts == [0], 'Initial-state convention')
    return table

def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {t}\n'
        for (q, b), (w, d, t) in sorted(table.items()))).encode('ascii')

def incoming(table, target):
    return sorted((key, value) for key, value in table.items() if value[2] == target)

def census(table, count, halt=254):
    states = {q for q, _ in table}
    need(len(states) == count and 0 in states and halt not in states, 'State census')
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Complete binary table')
    need({t for w, d, t in table.values()} - states == {halt}, 'Target closure')
    queue, seen = [0], {0}
    for q in queue:
        for bit in (0, 1):
            t = table[q, bit][2]
            if t != halt and t not in seen:
                seen.add(t)
                queue.append(t)
    need(seen == states, 'Graph-unreachable working state')
    return sorted(states)

def occurrences(root, table, target):
    found = []
    def visit(node, q, path):
        if q == target:
            found.append(path)
            return
        if L.leaf(node):
            return
        for bit in (0, 1):
            w, d, t = table[q, bit]
            if (w, d) == (bit, 1):
                visit(node[bit], t, path + str(bit))
    visit(root, 84, '')
    return found

def source_check(root, primitive_word, graph):
    rows = L.sites(root)
    need([r[1:] for r in rows] == primitive_word, 'Primitive word changed')
    need(L.graph_intervals(rows) == graph, 'Interval control graph changed')
    need(L.graph_arithmetic(rows)[0] == graph, 'Binary control graph changed')
    return rows

def rotate(root, table, p, q, side, primitive_word, graph):
    paths = occurrences(root, table, p)
    need(paths, 'No source occurrence of rotation root')
    need(incoming(table, q) == [((p, side), (side, 1, q))], 'Additional inner entry')
    need(all(table[r, b][:2] == (b, 1) for r in (p, q) for b in (0, 1)),
         'Impure rotation state')
    sizes = []
    for path in paths:
        node = L.subtree(root, path)
        if side == 0:
            a, b = node[0]
            c = node[1]
            replacement = (a, (b, c))
        else:
            a = node[0]
            b, c = node[1]
            replacement = ((a, b), c)
        need(all(L.boundary(n) == (0, 0, False) for n in (a, b, c)),
             'Escaping source factor')
        sizes.append([len(L.sites(n)) for n in (a, b, c)])
        root = L.replace(root, path, replacement)
    if side == 0:
        a, b, c = table[q, 0][2], table[q, 1][2], table[p, 1][2]
        table.update({(p, 0): (0, 1, a), (p, 1): (1, 1, q),
                      (q, 0): (0, 1, b), (q, 1): (1, 1, c)})
    else:
        a, b, c = table[p, 0][2], table[q, 0][2], table[q, 1][2]
        table.update({(p, 0): (0, 1, q), (p, 1): (1, 1, c),
                      (q, 0): (0, 1, a), (q, 1): (1, 1, b)})
    source_check(root, primitive_word, graph)
    return root, {'outer': p, 'inner': q, 'side': side, 'paths': paths,
                  'factor_sizes': sizes, 'metrics': L.metrics(root)}

def write_machine(out, stem, table, root, count):
    states = census(table, count)
    mapping = {q: i for i, q in enumerate(states)}
    mapping[254] = count
    dense = {(mapping[q], b): (w, d, mapping[t])
             for (q, b), (w, d, t) in table.items()}
    census(dense, count, count)
    blobs = {stem + '.native.tm': encode(table), stem + '.tm': encode(dense),
             stem + '.sites.json': L.compact(L.sites(root))}
    for name, raw in blobs.items():
        need(digest(raw) == EXPECTED[name], 'Frozen result mismatch: ' + name)
        (out / name).write_bytes(raw)
    (out / (stem + '.state_map.json')).write_text(json.dumps({
        'native_to_dense': mapping, 'dense_to_native': {v: k for k, v in mapping.items()},
        'native_halt': 254, 'dense_halt': count}, indent=2) + '\n')
    return {'working_states': count, 'rows': len(table), 'source': L.metrics(root),
            'sha256': {name: digest(raw) for name, raw in blobs.items()}}

def build(output):
    out = Path(output)
    out.mkdir(parents=True, exist_ok=True)
    parent = ROOT / 'comparison/Research'
    need(digest((parent / 'u211.native.tm').read_bytes()) == PARENT_TABLE, 'Parent table')
    need(digest((parent / 'sites.json').read_bytes()) == PARENT_SOURCE, 'Parent source')
    table = parse(parent / 'u211.native.tm')
    census(table, 211)
    rows = json.loads((parent / 'sites.json').read_text())
    root = L.tree(rows)
    primitive_word, graph = [r[1:] for r in rows], L.graph_intervals(rows)
    source_check(root, primitive_word, graph)
    ledger210 = []
    for p, q, side in ROTATIONS_210:
        root, record = rotate(root, table, p, q, side, primitive_word, graph)
        ledger210.append(record)
    (out / 'u210_prefold211.native.tm').write_bytes(encode(table))
    need(incoming(table, 218) == [((q, 0), (0, 1, 218)) for q in (158, 163, 211)],
         'Missing predecessor-zero guard')
    table = {(q, b): (w, d, 157 if t == 218 else t)
             for (q, b), (w, d, t) in table.items() if q != 218}
    result210 = write_machine(out, 'u210', table, root, 210)

    # Eight unchanged closed factors; the E factor has the certified zero tag.
    paths = occurrences(root, table, 174)
    need(paths == ['0011001110101011111111'], 'Bulk reassociation root')
    path = paths[0]
    node = L.subtree(root, path)
    a = node[0][0]
    b = node[0][1][0]
    c = node[0][1][1][0]
    d = node[0][1][1][1][0]
    e, f = node[0][1][1][1][1]
    g, h = node[1]
    factors = (a, b, c, d, e, f, g, h)
    need(node == ((a, (b, (c, (d, (e, f))))), (g, h)), 'Old eight-factor shape')
    need(all(L.boundary(n) == (0, 0, False) for n in factors), 'Nonclosed factor')
    sizes = [len(L.sites(n)) for n in factors]
    need(sizes == [26, 134, 52, 108, 136, 27, 103, 134], 'Factor identities')
    root = L.replace(root, path, ((a, (b, (c, d))), (e, ((f, g), h))))
    bulk = {(204, 1): (1, 1, 146), (217, 0): (0, 1, 220),
            (217, 1): (1, 1, 214), (214, 0): (0, 1, 216),
            (214, 1): (1, 1, 163), (216, 0): (0, 1, 90), (216, 1): (1, 1, 211)}
    table.update(bulk)
    source_check(root, primitive_word, graph)
    ledger209 = [{'type': 'eight_closed_factors', 'path': path, 'sizes': sizes,
                  'changes': [[q, b, *v] for (q, b), v in sorted(bulk.items())]}]
    for p, q, side in ROTATIONS_209:
        root, record = rotate(root, table, p, q, side, primitive_word, graph)
        ledger209.append(record)
    need(table[171, 0] == (0, -1, 7), 'Arithmetic entrance changed early')
    table[171, 0] = (0, -1, 205)
    (out / 'u209_prefold210.native.tm').write_bytes(encode(table))
    need(table[216, 0] == (0, 1, 90) and table[180, 0] == (0, 1, 152), 'Zero branches')
    need(table[216, 1] == table[180, 1] == (1, 1, 211), 'Common one branch')
    need(incoming(table, 216) == [((214, 0), (0, 1, 216))], 'Zero tag')
    need(incoming(table, 180) == [((132, 1), (1, 1, 180)),
                                 ((199, 1), (1, 1, 180))], 'One tag')
    table = {(q, b): (w, d, 216 if t == 180 else t)
             for (q, b), (w, d, t) in table.items() if q != 180}
    table[216, 0] = (0, -1, 211)
    result209 = write_machine(out, 'u209', table, root, 209)
    result = {'status': 'EXACT_RECONSTRUCTION_PASS', 'u210': result210, 'u209': result209,
              'u210_rotations': ledger210, 'u209_transformations': ledger209}
    (out / 'construction.json').write_text(json.dumps(result, indent=2) + '\n')
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'build')
    print(json.dumps(build(parser.parse_args().output), indent=2))
