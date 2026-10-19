#!/usr/bin/env python3
"""Check frame closure for a rebuilt semantic grammar, independently of the VM.

The integer pointer argument adapts the attributed source68
code/verify_machine_frame245.py to arbitrary certified reassociations.  It
imports no source decoder, symbolic executor, or machine interpreter.  Runtime
macro proofs and the exact blank run are separate, explicitly required inputs.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def table(path):
    rows, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            a, b, w, d, t = line.split()
            a, b, w, t = map(int, (a, b, w, t))
            assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            assert (a, b) not in rows
            rows[a, b] = w, d, t
    assert start is not None
    return rows, start


def verify(folder):
    def read(name):
        return json.loads((folder / name).read_text())
    audit = read('semantic-audit.json')
    assert audit['status'] == 'PASS_SOURCE_AFFINE_AND_BOOT'
    assert audit['actual_table_macro_inductions']['status'] == 'PASS'
    assert audit['affine_all_cases']['status'] == 'PASS'
    new, start = table(folder / 'machine.tm')
    old, old_start = table(folder / 'machine_old.tm')
    states = audit['working_states']
    assert start == 0 and old_start == 95
    assert {q for q, b in new} == set(range(states))
    assert len(new) == 2 * states
    assert {q for w, d, q in new.values()} - set(range(states)) == {states}
    mapping = {int(k): v for k, v in read('renumbering.json')['old_to_canonical'].items()}
    assert mapping[95] == 0 and mapping[254] == states
    assert {(mapping[q], b): (w, d, mapping[t]) for (q, b), (w, d, t) in old.items()} == new
    for name, key in [('machine.tm', 'machine_sha256'), ('machine_old.tm', 'old_machine_sha256')]:
        assert hashlib.sha256((folder / name).read_bytes()).hexdigest() == audit[key]

    sites = read('sites_logical.json')
    physical = read('sites_physical.json')
    assert [[p, op, PHYSICAL[r] if op in ('CI', 'CD') else r] for p, op, r in sites] == physical
    leaves = {p: (op, r) for p, op, r in sites}
    assert len(leaves) == len(sites) == 6460
    assert all(p and set(p) <= {'0', '1'} for p in leaves)
    assert all(0 <= r < 9 for p, op, r in sites if op in ('CI', 'CD'))
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    assert not prefixes.intersection(leaves)
    assert len(prefixes) == 6459
    assert all(p + b in prefixes or p + b in leaves for p in prefixes for b in '01')
    depth = max(map(len, leaves))
    zero_run = max(len(run) for p in leaves for run in p.split('1'))
    assert (depth, zero_run) == (audit['maximum_depth'], audit['maximum_zero_run'])
    padding = audit['padding']
    assert padding >= depth

    def decode(word):
        path = ''
        for i in range(depth):
            path += word[i] if i < len(word) else '0'
            if path in leaves:
                assert '1' not in word[len(path):]
                return path
        raise AssertionError('Complete source tree did not decode its zero extension.')

    def add_one(word):
        width = len(word)
        number = int(word, 2) if width else 0
        carry = number + 1 == 2 ** width
        residue = (number + 1) % 2 ** width
        return (format(residue, f'0{width}b') if width else ''), carry

    def cut(word, bit, count):
        if count == 0:
            return word
        indices = [i for i, b in enumerate(word) if b == bit]
        return word[:indices[-count]] if len(indices) >= count else ''

    normalized, case = 0, 0
    carries, deltas = [], Counter()
    minimum_padding = padding
    for path, op, register in sites:
        for zero in ((True, False) if op == 'CD' else (None,)):
            extra = int(op == 'CD' and not zero)
            if op == 'CI' or (op == 'CD' and not zero):
                successor, overflow = add_one(path)
            elif op == 'CD':
                successor, overflow = add_one(cut(path, '0', 1))
            elif op == 'CB':
                successor, overflow = add_one(cut(path, '0', register))
            elif op == 'CC':
                successor, overflow = cut(path, '1', register), False
            else:
                assert op == 'CH'
                case += 1
                continue
            delta = extra + int(overflow)
            deltas[delta] += 1
            if overflow:
                carries.append(case)
            canonical = decode(successor)
            suffix = padding + delta - len(successor)
            minimum_padding = min(minimum_padding, suffix)
            assert suffix >= 0
            # The same arbitrary n zeroes may be appended to both sides.
            assert successor + '0' * suffix == canonical + '0' * (padding + delta - len(canonical))
            normalized += 1
            case += 1
    assert (normalized, case) == (8390, 8391)
    root = decode('')
    assert root + '0' * (padding - len(root)) == '0' * padding

    boot = read('blank_boot.json')
    assert boot['status'] == 'PASS' and boot['sparse_dense_exact_agreement']
    assert boot['all_other_cells_zero']
    assert boot['start'] == 95 and boot['dispatcher'] == 96 and boot['pc'] == ''
    assert boot['marker'] == boot['head'] - 1
    assert boot['header'] - boot['head'] == boot['header_distance'] >= padding
    values, spare = boot['physical_registers'], boot['spare_values']
    assert len(values) == 9 and spare
    assert all(isinstance(v, int) and v >= 0 for v in values + spare)
    logical = [values[r] for r in PHYSICAL]
    assert logical == boot['logical_registers']
    assert logical[1] == logical[2] == logical[5] == 0
    ones, position = {boot['marker'], boot['header']}, boot['header'] + 1
    for value in values + spare:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    assert sorted(ones) == boot['all_one_positions']
    assert len(ones) == boot['one_count']
    assert audit['affine_all_cases']['minimum_literal_steps'] > 0
    return dict(status='PASS', working_states=states, canonical_transitions=len(new),
                renumbering_exact=True, source_instruction_sites=len(sites),
                nonhalting_successors_normalized=normalized, guarded_cases=case,
                maximum_depth=depth, maximum_zero_run=zero_run,
                overflow_case_indices=carries, gap_increment_histogram=dict(deltas),
                minimum_constant_padding_after_successor=minimum_padding, padding=padding,
                initial_gap=boot['header_distance'], initial_affine_parameter=boot['header_distance']-padding,
                blank_steps=boot['blank_steps'], initial_logical_registers=logical,
                spare_count=len(spare), exact_entire_frame_reconstructed=True,
                parameter_update='n_next = n + positive_decrement + full_path_carry',
                spare_update='K_next = K+1 on increment, K otherwise',
                scope='Independent finite pointer/frame closure; exact-table macro inductions and source bisimulation are separate checked inputs; no proof-assistant endpoint.')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--machine', type=Path, required=True)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions are required.')
    result = verify(args.machine)
    value = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(value)
    print(value, end='')
