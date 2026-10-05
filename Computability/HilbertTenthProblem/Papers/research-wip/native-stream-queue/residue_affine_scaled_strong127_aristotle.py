#!/usr/bin/env python3
"""Fresh static construction only; freeze after own checks, never replay later.

No source-array interpreter, polynomial interpreter, degree propagator, or
predecessor import is present. Arrays are inert producer/dependency records.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


PINS = {
    'residue_affine_binary_lane128_tesla.md': 'b5d93830a38426f5ac4129d04888efa94b0086932277b969dd810bff0ad1120c',
    'residue_affine_binary_lane128_tesla.json': 'daa90bb7113164e564444eaca6de7025edaddd0e27fde02f93c9e7b11f4d41ea',
    'residue_affine_binary_lane128_tesla.py': '14f0119560751ca783faceeff0b0bc35d8f095deeaf528641883794c0f7f8823',
    'review_residue_affine_binary_lane128_aristotle.md': '4be186c471e588c16d181f9da910c6a71b84969192a871737e737565f6360d8d',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'neary_woods_scaled_strong249_tesla.md': '2230f44faee7e2ecebb0ce29722462f121a49e85addf3740d8b8b54efd7bc8a4',
    'neary_woods_scaled_strong249_degree_correction_tesla.md': 'ada1718ff4e93eb4b48e50d1362b8912973c6d629e1f724878a4e12804a39f11',
}
PORTS = ['input', 'target', 'edge0_hat', 'edge1_hat', 'quotient_hat',
         'product0_hat', 'height_slack', 'global_slack', 'native__F0',
         'native__F1', 'native__F2', 'native__odd_half', 'native__bound_beta',
         'native__eta', 'native__zeta', 'native__f', 'native__o',
         'native__y_aux', 'native__h', 'native__ga', 'native__i',
         'native__j', 'native__tau_gap']
OLD_BLOCK = [
    ['native__ic2', '*', 'native__i', 'native__c2'],
    ['native__ic22', '*', 'native__ic2', 'native__ic2'],
    ['native__normalized_strong_Q', '*', 'native__A', 'native__ic22'],
    ['native__f_square_minus_one', '-', 'native__L16', 'native__normalized_strong_Q'],
    ['native__R16', '*', 'native__A', 'native__normalized_strong_Q'],
]
NEW_BLOCK = [
    ['native__scaled_aux_root', '*', 'native__i', 'native__Ac2'],
    ['native__R16', '*', 'native__scaled_aux_root', 'native__scaled_aux_root'],
    ['native__scaled_f_square', '*', 'native__A', 'native__L16'],
    ['native__f_square_minus_one', '-', 'native__scaled_f_square', 'native__R16'],
]
GUARDS = [
    ['native__L16', '*', 'native__f', 'native__f'],
    ['native__c2', '*', 'native__R10a', 'native__R10a'],
    ['native__Ac2', '*', 'native__A', 'native__c2'],
    ['native__R12', '+', 'native__UM', 'native__sn2'],
    ['native__UM', '*', 'native__wn2', 'native__sn2'],
    ['native__wn2', '*', 'native__bs_X_bound', 'native__q'],
    ['native__bs_X_bound', '+', 'native__bs_packed', 'native__bound_beta'],
    ['native__sn2', '*', 'native__bs_odd', 'native__q'],
    ['native__bs_odd', '+', 'native__bs_even', 1],
    ['native__bs_even', '*', 2, 'native__odd_half'],
    ['native__a_square', '*', 'native__R12', 'native__R12'],
    ['native__a4', '*', 4, 'native__R12'],
    ['native__a4m5', '+', 'native__a4', 3],
    ['native__A', '+', 'native__a_square', 'native__a4m5'],
    ['native__L17', '*', 'native__R16', 'native__aux_square_gap'],
    ['native__P17', '+', 'native__L17', 'native__aux_y2'],
    ['native__normalized_norm_units', '*', 'native__norm_unit_product2', 'native__f_square_minus_one'],
    ['norm_outer_positive', '+', 'norm_sum3', 1],
    ['norm_outer_product', '*', 'native__coupled_all_units', 'norm_outer_positive'],
    ['norm_output', '-', 'norm_outer_product', 1],
]


def ck(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def consumers(rows, name):
    return sorted(r[0] for r in rows if name in r[2:])


def ledger(rows, output):
    defined = set(PORTS)
    by_name = {}
    counts = Counter()
    for row in rows:
        ck(len(row) == 4, 'row arity')
        name, op, x, y = row
        ck(name not in defined, 'duplicate producer ' + name)
        ck(op in ['+', '-', '*'], 'operator')
        for atom in [x, y]:
            ck(type(atom) is int or (type(atom) is str and atom in defined), 'unpaid dependency ' + name)
        defined.add(name)
        by_name[name] = row
        counts['M' if op == '*' else 'A'] += 1
    live = set()
    work = [output]
    while work:
        name = work.pop()
        if name in live:
            continue
        live.add(name)
        if name in by_name:
            work.extend(a for a in by_name[name][2:] if type(a) is str)
    ck(set(by_name) <= live, 'dead producer')
    ck(set(PORTS) <= live, 'dead supplied port')
    return dict(operations=len(rows), multiplications=counts['M'],
                additions_subtractions=counts['A'], output=output,
                positive_witnesses=21, supplied_ports=23,
                all_rows_live=True, all_ports_live=True,
                canonical_rows_sha256=sha(json.dumps(rows, separators=(',', ':')).encode()))


def build(parent_rows):
    by_name = {r[0]: r for r in parent_rows}
    for row in OLD_BLOCK + GUARDS:
        ck(by_name.get(row[0]) == row, 'literal guard ' + row[0])
    expected = {
        'native__ic2': ['native__ic22'],
        'native__ic22': ['native__normalized_strong_Q'],
        'native__normalized_strong_Q': ['native__R16', 'native__f_square_minus_one'],
        'native__f_square_minus_one': ['native__normalized_norm_units'],
        'native__R16': ['native__L17'],
    }
    for name, uses in expected.items():
        ck(consumers(parent_rows, name) == uses, 'private consumers ' + name)
    old_names = {r[0] for r in OLD_BLOCK}
    new_rows = []
    for row in parent_rows:
        if row[0] == 'native__normalized_strong_Q':
            new_rows.extend([r[:] for r in NEW_BLOCK])
        if row[0] in old_names:
            continue
        if row[0] == 'norm_output':
            new_rows.append(['norm_output', '-', 'norm_outer_product', 'native__A'])
        else:
            new_rows.append(row[:])
    new_by_name = {r[0]: r for r in new_rows}
    deleted = sorted(set(by_name) - set(new_by_name))
    added = sorted(set(new_by_name) - set(by_name))
    edited = sorted(n for n in set(by_name) & set(new_by_name) if by_name[n] != new_by_name[n])
    ck(deleted == ['native__ic2', 'native__ic22', 'native__normalized_strong_Q'], 'deleted names')
    ck(added == ['native__scaled_aux_root', 'native__scaled_f_square'], 'new names')
    ck(edited == ['native__R16', 'native__f_square_minus_one', 'norm_output'], 'edited names')
    literal = sum(by_name.get(r[0]) == r for r in new_rows)
    ck(literal == len(parent_rows) - 6, 'literal retention')
    ck(consumers(new_rows, 'native__scaled_aux_root') == ['native__R16'], 'new auxiliary-root privacy')
    ck(consumers(new_rows, 'native__scaled_f_square') == ['native__f_square_minus_one'], 'new square privacy')
    for row in parent_rows:
        if row[0] not in old_names | {'norm_output'}:
            ck(new_by_name[row[0]] == row, 'protected retained row')
    return new_rows, dict(deleted_names=deleted, new_names=added,
                         edited_names=edited, literal_retained_rows=literal,
                         old_private_consumer_guards=expected)


def receipt(root):
    dependencies = []
    for name, pin in PINS.items():
        data = (root / name).read_bytes()
        ck(sha(data) == pin, 'dependency pin ' + name)
        dependencies.append(dict(file=name, sha256=pin, bytes=len(data)))
    data = (root / 'residue_affine_binary_lane128_tesla.json').read_bytes()
    parent = json.loads(data)
    parent_copy = json.dumps(parent, sort_keys=True)
    ck(parent['external_positive_inputs'] + parent['outer_positive_witnesses'] + parent['native_positive_witnesses'] == PORTS, 'complete roles')
    ck(parent['fixed_table'] == [[3, 2], [1, 1]], 'fixed map')
    inherited = []
    for dep in parent['dependencies']:
        path = root / Path(dep['path']).name
        raw = path.read_bytes()
        ck(sha(raw) == dep['sha256'] and len(raw) == dep['bytes'], 'inherited byte pin')
        inherited.append(dict(file=path.name, sha256=sha(raw), bytes=len(raw)))
    variants = {}
    degrees = {'power3': 668, 'power4': 824, 'power3_empty': 669}
    for name in ['power3', 'power4', 'power3_empty']:
        old = parent['variants'][name]['source']
        rows, delta = build(old)
        output = 'empty_output' if name.endswith('_empty') else 'norm_output'
        old_ledger = ledger(old, output)
        new_ledger = ledger(rows, output)
        empty = name.endswith('_empty')
        ck((new_ledger['multiplications'], new_ledger['additions_subtractions']) == ((61, 68) if empty else (60, 67)), 'new cost')
        ck(old_ledger['operations'] == new_ledger['operations'] + 1, 'one paid saving')
        value = dict(source=rows, ledger=new_ledger, changes=delta,
                     manual_degree_upper_bound=degrees[name],
                     whole_polynomial_identity='new_output = native__A * old_output',
                     positive_zero_map='identity on all 23 supplied coordinates')
        if not empty:
            value['certificate'] = dict(operations=113, multiplications=55,
                                        additions_subtractions=58, comparisons=5)
        variants[name] = value
    ck(variants['power3_empty']['source'][:-2] == variants['power3']['source'], 'empty extension')
    a = variants['power3']['source']
    b = variants['power4']['source']
    diff = [x[0] for x, y in zip(a, b) if x != y]
    ck(diff == ['scale_power_46'], 'control-only power difference')
    ck(json.dumps(parent, sort_keys=True) == parent_copy, 'parent data immutability')
    ck(sha((root / 'residue_affine_binary_lane128_tesla.json').read_bytes()) == sha(data), 'parent byte immutability')
    return dict(status='fresh static source construction; freeze after pre-freeze checks',
                execution_scope='No saved-array evaluation or symbolic/degree propagation; no predecessor import or execution. No future replay after freezing.',
                author_helper_sha256=sha(Path(__file__).read_bytes()),
                dependencies=dependencies, inherited_parent_dependency_pins=inherited,
                fixed_table=parent['fixed_table'], external_positive_inputs=PORTS[:2],
                outer_positive_witnesses=parent['outer_positive_witnesses'],
                native_positive_witnesses=parent['native_positive_witnesses'],
                old_block=OLD_BLOCK, new_block=NEW_BLOCK, variants=variants,
                manual_degree_note='Handwritten proof bounds: parent586/722 plus positive multiplier82/102; empty adds1. Not computed from arrays.',
                scope='Fixed shortcut-Collatz finite positive orbits; no universal-computation, termination, or universal gate-bound claim.')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', type=Path)
    mode.add_argument('--expect', type=Path)
    args = ap.parse_args()
    result = receipt(args.root)
    encoded = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.write:
        args.write.write_text(encoded)
    else:
        ck(args.expect.read_text() == encoded, 'exact deterministic receipt')
    print('PASS: 383 live emitted rows; costs127/127/129; static metadata only.')


if __name__ == '__main__':
    main()
