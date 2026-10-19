#!/usr/bin/env python3
"""Reconstruct K229, K228 and K227 from the frozen K230 release.

No optimizer, search, network, or proof assistant is needed. The complete
runtime theorem is checked separately by verification/verify_runtime.py.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'verification'))
import source_tools as b

K230_SHA = 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
SOURCE_SHA = '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
K229_SHA = 'b96eeef7cfd5083f3ab737fa7885482ebcae2a947bce5fb20e54a547dc254d32'
K228_SHA = '7f5153ac9360cbab06a4c8ce0a01d55228a4f4e32dcd83a3234d5ef94c2f35a6'
K227_SHA = '175d6d4df7b988b45253e0a3bcb2651648b55a0ca1efddd4d5c6100ff71b8f46'
POSTTEST_PATHS = [
    '111010010010111111000011', '11101001001011111110011',
    '1110100101100011', '111110011',
]


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def write_json(p, value, compact=False):
    p.write_bytes(b.json_bytes(value, compact))


def k230_table(path):
    b.require(sha(path) == K230_SHA, 'Wrong pinned K230 table')
    table = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            b.require(start is None, 'Duplicate start')
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, r, w, d, z = line.split()
            q, r, w, z = map(int, (q, r, w, z))
            b.require((q, r) not in table and d in ('L', 'R') and w in (0, 1), 'Bad row')
            table[q, r] = w, 1 if d == 'R' else -1, z
    b.require(start == 0 and set(table) == {(q, r) for q in range(230) for r in (0, 1)},
              'Wrong K230 start or census')
    b.require({z for w, d, z in table.values()} - set(range(230)) == {230}, 'Wrong halt')
    return table


def normalize_source(path):
    b.require(sha(path) == SOURCE_SHA, 'Wrong pinned K230 source')
    opcodes = {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB', 'EContinue': 'CC', 'EHalt': 'CH'}
    rows = []
    for pc, instruction in json.loads(path.read_text()):
        fields = instruction.split()
        rows.append((pc, opcodes[fields[0]], int(fields[1]) if len(fields) == 2 else None))
    b.require(len(rows) == 5125, 'Wrong original source census')
    return rows


def posttest(root):
    before = ((('CD', 6), (('CI', 5), ('CC', 2))), ('CI', 5))
    after = (('CI', 5), (('CD', 6), ('CC', 2)))
    b.require(b.boundary(before) == b.boundary(after) == (0, 0, False), 'Loop is not closed')
    paths = []
    def replace(t, pc=''):
        if t == before:
            paths.append(pc)
            return after
        return t if b.is_leaf(t) else (replace(t[0], pc+'0'), replace(t[1], pc+'1'))
    newroot = replace(root)
    b.require(paths == POSTTEST_PATHS, 'Unexpected loop occurrences')
    return newroot, dict(paths=paths, before=before, after=after,
                        effect='(R6,R5)=(n,m) -> (0,m+n+1), all natural n,m',
                        primitive_duration='3*n+2', other_registers='unchanged',
                        proof='verification/check_loop_identity.py and source/loop_identity.md')


def edits(old, new):
    return [dict(row=k, before=old.get(k), after=v)
            for k, v in sorted(new.items()) if old.get(k) != v]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--reference-dir', type=Path, default=ROOT/'reference/k230-rocq')
    a = p.parse_args()
    a.output_dir.mkdir(parents=True, exist_ok=True)
    kt = k230_table(a.reference_dir/'machine/k230.tm')
    mapping = {int(k): v for k, v in json.loads((ROOT/'source/label_map.json').read_text())['k230_to_label'].items()}
    b.require(set(mapping) == set(range(231)) and len(set(mapping.values())) == 231,
              'Label correspondence is not a total bijection')
    b.require((mapping[0], mapping[84], mapping[230]) == (95, 96, 254), 'Wrong interfaces')
    original = {(mapping[q], r): (w, d, mapping[z]) for (q, r), (w, d, z) in kt.items()}
    rows0 = normalize_source(a.reference_dir/'machine/sites230.json')
    root0 = b.tree(rows0)
    root1, loop = posttest(root0)
    rows1 = b.sites(root1)
    b.require(original[142, 0] == (0, 1, 37) and original[142, 1] == (1, 1, 72),
              'Posttest decoder precondition fails')
    rotated230 = original | {(142, 0): (0, 1, 72), (142, 1): (1, 1, 17)}
    # Interpreter fold: the old90 entry is shared with72, using tape context.
    t229 = {(q, r): (w, d, 72 if z == 90 else z)
            for (q, r), (w, d, z) in rotated230.items() if q != 90}
    t229[72, 0] = 0, -1, 144
    t229[72, 1] = 1, -1, 36
    b.require(len(t229) == 458 and b.sha(b.encode(t229)) == K229_SHA, 'Wrong K229')
    # Arithmetic fold: the runtime proof supplies the complete global contract.
    t228 = {(q, r): (w, d, 80 if z == 169 else z)
            for (q, r), (w, d, z) in t229.items() if q != 169}
    t228[80, 0] = 0, -1, 106
    t228[91, 1] = 1, -1, 167
    b.require(len(t228) == 456 and b.sha(b.encode(t228)) == K228_SHA, 'Wrong K228')
    # One closed source reassociation prepares the boundary-state sharing.
    root2, basis228, rotation = b.stage(root1, t228, 184, 181, 'right')
    rows2 = b.sites(root2)
    b.require(b.graph(rows1)[1:] == b.graph(rows2)[1:], 'Source control graph changed')
    b.require([r[1:] for r in rows1] == [r[1:] for r in rows2], 'Instruction order changed')
    incoming = [(q, r, w, d) for (q, r), (w, d, z) in sorted(basis228.items()) if z == 218]
    b.require(incoming and all(d == 1 for q, r, w, d in incoming),
              'The split selector must be the bit just written to the left')
    t227 = {(q, r): (w, d, (242 if w == 0 else 179) if z == 218 else z)
            for (q, r), (w, d, z) in basis228.items() if q != 218}
    t227[179, 1] = 1, -1, 215
    t227[242, 0] = 0, -1, 165
    t227[242, 1] = 1, -1, 195
    b.require(len(t227) == 454 and b.sha(b.encode(t227)) == K227_SHA, 'Wrong K227')
    inv = {v: k for k, v in mapping.items()}
    mappings = {}
    for n, table in ((229, t229), (228, t228), (227, t227)):
        # Retain original K230 ordering, with absent states removed.
        states = {q for q, r in table}
        order = sorted(states, key=lambda q: inv[q])
        b.require(order[0] == 95 and len(order) == n, 'Wrong canonical order')
        ren = {q: i for i, q in enumerate(order)} | {254: n}
        canonical = {(ren[q], r): (w, d, ren[z]) for (q, r), (w, d, z) in table.items()}
        b.require(set(canonical) == {(q, r) for q in range(n) for r in (0, 1)}, 'Partial canonical table')
        (a.output_dir/f'k{n}_inherited.tm').write_bytes(b.encode(table))
        (a.output_dir/f'k{n}.tm').write_bytes(b.encode(canonical, 0))
        write_json(a.output_dir/f'k{n}_renumbering.json',
                   dict(inherited_to_canonical=ren, canonical_to_inherited=order+[254],
                        start=0, dispatcher=ren[96], halt=n))
        mappings[str(n)] = dict(canonical_sha256=b.sha(b.encode(canonical, 0)),
                               inherited_sha256=b.sha(b.encode(table)),
                               dispatcher=ren[96], halt=n, rows=2*n)
    for name, table in (('k230_inherited', original), ('k230_posttest_inherited', rotated230),
                        ('k228_rotated_inherited', basis228)):
        (a.output_dir/(name+'.tm')).write_bytes(b.encode(table))
    for name, rows in (('k230', rows0), ('k228', rows1), ('k227', rows2)):
        write_json(a.output_dir/(name+'_sites_logical.json'), rows, compact=True)
        (a.output_dir/(name+'_sites.txt')).write_text(''.join(
            f'{pc} {op} {arg if arg is not None else -1}\n' for pc, op, arg in rows))
    write_json(a.output_dir/'posttest_source_certificate.json', loop)
    write_json(a.output_dir/'rotation227.json', rotation)
    receipt = dict(status='PASS_EXACT_RECONSTRUCTION_AND_SOURCE_GRAPH',
                   k230_commit='3142e4dd980f0be12f4abb636c4ae2528afc17eb',
                   baseline_table_sha256=K230_SHA, baseline_source_sha256=SOURCE_SHA,
                   machines=mappings, metrics230=b.metrics(root0), metrics228=b.metrics(root1),
                   metrics227=b.metrics(root2), k230_to_k228_edits=edits(original, t228),
                   k228_to_k227_edits=edits(t228, t227), split_incoming=incoming,
                   deleted_inherited_states=[90, 169, 218], deleted_k230_states=[inv[q] for q in (90,169,218)],
                   source_reassociation_graph_identical=True,
                   scope='Exact finite construction and source checks. Uniform loop induction, '
                         'local folds, unbounded binary runtime, blank startup, and logical '
                         'calibration are separate included checks.')
    write_json(a.output_dir/'construction.json', receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    b.require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    main()
