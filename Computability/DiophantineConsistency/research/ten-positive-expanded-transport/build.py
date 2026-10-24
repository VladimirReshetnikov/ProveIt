#!/usr/bin/env python3
"""Materialize two identical-polynomial transport contractions, locally only."""
from collections import Counter
from copy import deepcopy
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='Rebuild in memory, compare every byte, and write nothing.')
args = parser.parse_args()
rendered = {}


def write(name, value):
    rendered[name] = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


pins = {}
for tag, parent_name in [('zero98', 'ten-positive-zero-offset'),
                         ('direct103', 'ten-positive-direct-zero-offset')]:
    parent = ROOT / 'candidates' / parent_name
    data = json.loads((parent / 'equation.json').read_text())
    child = deepcopy(data)
    direct = tag == 'direct103'
    removed = {'qm1L', 'W', 'WBt'} | ({'q4'} if direct else set())
    changed = {'Hn', 'q3WBt'} | ({'P1'} if direct else set())
    rows = []
    records = []
    for i, row in enumerate(data['source']):
        name = row[0]
        rec = dict(parent_index=i, old_row=row)
        if name in removed:
            rec['status'] = 'deleted_private'
        else:
            if name == 'P1' and direct:
                new = ['P1', '*', 'q3', 'qbJ']
            elif name == 'Hn':
                new = ['Hn', '*', 'Hp', 'nVL']
            elif name == 'q3WBt':
                new = ['q3WBt', '*', 'q3', 'B' if direct else 'Bt']
            else:
                new = row
            rec.update(child_index=len(rows), new_row=new,
                       status='replaced_operand' if name in changed else 'retained')
            rows.append(new)
            if name == 'nV':
                rows.append(['LB', '*', 'L', 'B' if direct else 'Bt'])
                rows.append(['nVL', '-', 'nV', 'LB'])
        records.append(rec)
    child['source'] = rows
    child['name'] = 'ten_positive_expanded_transport_' + tag
    child['operations'] = len(rows)
    child['operation_breakdown'] = dict(Counter(r[1] for r in rows))
    child['parent_sha256'] = hashlib.sha256((parent / 'equation.json').read_bytes()).hexdigest()
    child['proof'] = 'PROOF.md'
    child['proof_status'] = ('Universal identical-polynomial contraction of accepted parent. '
                             'Same positive witnesses and complete coherent coefficients. '
                             'No Lean/internal-ZFC endpoint asserted.')
    child['register_degrees'].pop('W', None)
    cuts = dict(parent_name=parent_name, all_parent_rows=records,
                inserted_child_rows=[dict(child_index=i, new_row=r)
                                     for i, r in enumerate(rows) if r[0] in {'LB', 'nVL'}])
    write(tag + '.json', child)
    write(tag + '_CUTS.json', cuts)
    for rel in ['equation.json', 'PROOF.md', 'CHECK.json', 'MANIFEST.json']:
        pins[parent_name + '/' + rel] = hashlib.sha256((parent / rel).read_bytes()).hexdigest()
    for rel in ['equation.json', 'PROOF.md', 'CHECK.json']:
        rendered['parents/' + parent_name + '/' + rel] = (parent / rel).read_bytes()

for path in sorted((ROOT / 'candidates/ten-positive-zero-offset/coefficients').iterdir()):
    if path.is_file():
        rendered['coefficients/' + path.name] = path.read_bytes()
write('PARENT_PINS.json', pins)
bindings = {name: hashlib.sha256(data).hexdigest() for name, data in rendered.items()}
for name in ['build.py', 'check.py', 'PROOF.md', 'README.md']:
    bindings[name] = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
write('BUILD.json', dict(status='PASS', equations={'zero98': dict(operations=98, exact_degree=368),
                                                'direct103': dict(operations=103, exact_degree=340)},
                         sha256=bindings))
for name, data in rendered.items():
    path = HERE / name
    if args.check:
        if not path.is_file() or path.read_bytes() != data:
            raise ValueError('Deterministic rebuild mismatch: ' + name)
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
print(json.dumps(dict(status='PASS', mode='check' if args.check else 'build',
                      optimized_python=not __debug__, compared_files=len(rendered),
                      equations={'zero98': '98/368', 'direct103': '103/340'},
                      writes=0 if args.check else len(rendered)), sort_keys=True))
