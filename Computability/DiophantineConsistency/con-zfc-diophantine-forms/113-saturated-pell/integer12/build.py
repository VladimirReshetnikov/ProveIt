#!/usr/bin/env python3
"""Build two exact integer-coordinate shears of the pinned scalar12 parents."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    'rational': '5e85d22284880b36b44d7f50ef1648fbcbff4154cc56ab8ae393611b89fa55dc',
    'integral': '0e30346f30a6539c3d5ace2f58135e3b2c3f12fc69ce47b6d72d5bdffe9ef75b',
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def produce(variant):
    raw = (HERE / 'parent' / (variant + '.json')).read_bytes()
    require(sha256(raw).hexdigest() == PINS[variant], 'pinned complete parent')
    parent = json.loads(raw)
    source, named = parent['nodes'], parent['named_registers']
    rows, mapping = [], {}

    def emit(row):
        rows.append(row)
        return len(rows) - 1

    for old, row in enumerate(source):
        if old == named['center']:
            shift = mapping[named['V']]
            if variant == 'integral':
                shift = emit(['mul', mapping[named['delta']], shift])
            shifted_n = emit(['add', mapping[named['n']], shift])
            scaled = emit(['mul', mapping[named['S']], shifted_n])
            mapping[old] = emit(['sub', scaled, mapping[named['Acarrier']]])
        elif row[0] in ('add', 'sub', 'mul'):
            mapping[old] = emit([row[0], mapping[row[1]], mapping[row[2]]])
        else:
            mapping[old] = emit(list(row))

    output = mapping[parent['output']]
    live, todo = set(), [output]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        if rows[i][0] in ('add', 'sub', 'mul'):
            todo.extend(rows[i][1:])
    order = sorted(live)
    reindex = {i: j for j, i in enumerate(order)}
    new_rows = [
        [row[0], reindex[row[1]], reindex[row[2]]]
        if row[0] in ('add', 'sub', 'mul') else row
        for i in order for row in [rows[i]]
    ]
    packet = deepcopy(parent)
    packet['nodes'] = new_rows
    packet['named_registers'] = {
        name: reindex[mapping[i]] for name, i in named.items()
        if mapping[i] in live
    }
    packet['output'] = reindex[output]
    counts = dict(Counter(r[0] for r in new_rows if r[0] in ('add', 'sub', 'mul')))
    bounds = []
    for r in new_rows:
        if r[0] in ('add', 'sub', 'mul'):
            bounds.append(bounds[r[1]] + bounds[r[2]] if r[0] == 'mul'
                          else max(bounds[r[1]], bounds[r[2]]))
        else:
            bounds.append(int(r[0] == 'variable'))
    packet.update(
        name='scalar12_' + variant + '_centered',
        operations=sum(counts.values()), operation_counts=counts,
        exact_degree=1200 if variant == 'integral' else 1184,
        syntactic_bound=bounds[packet['output']],
        parent_sha256=PINS[variant],
        parent_file='parent/' + variant + '.json',
        source_commit='84e16e43092614bae262ca59651cb9d77e31a255',
        shear='n_old=n+delta*V' if variant == 'integral' else 'n_old=n+V',
        ordinary_proof='PROOF.md',
        proof_status='Universal polynomial coordinate automorphism over Z^12; '
                     'inherits exactly the pinned parent ordinary calibration. '
                     'No new native calibration, Lean, or encoded object-ZFC proof.',
    )
    return packet


def encoded(x):
    return (json.dumps(x, indent=2, sort_keys=True) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    report = {}
    for variant in ('rational', 'integral'):
        packet = produce(variant)
        path = HERE / (variant + '_centered.json')
        data = encoded(packet)
        if args.check:
            require(path.read_bytes() == data, 'exact deterministic rebuild ' + path.name)
        else:
            path.write_bytes(data)
        report[variant] = {k: packet[k] for k in
                           ('operations', 'operation_counts', 'exact_degree', 'syntactic_bound')}
    print(json.dumps({'status': 'PASS', 'check': args.check, 'variants': report}, indent=2))


if __name__ == '__main__':
    main()
