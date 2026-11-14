#!/usr/bin/env python3
"""Independently verify the delivered reassociated PA194R literal machine.

Reads its native table and source paths, resolves the entire source graph by
two independent algorithms, and compares it with PA194F. The attributed
literal symbolic engine rederives four list lemmas and checks every primitive
outcome, including both decrement branches. A separate finite-support simulator
checks the entire blank-start tape. No compiler or arithmetic oracle is used.

Run from any directory; --output chooses the parent of the PA194R receipts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

if not __debug__:
    raise SystemExit('Assertions must be enabled; do not run Python with -O.')

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
sys.path.insert(0, str(HERE / 'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
import four_site_cut
sym.HEADER_BASE = 48
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
EXPECTED_DENSE_SHA = '8a9a8a30773f73b638a7c51da1afca9c9921371aea819d6a21f02d742f673a4e'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        q, bit, written, direction, target = line.split()
        q, bit, written, target = map(int, (q, bit, written, target))
        assert bit in (0, 1) and written in (0, 1)
        assert direction in ('L', 'R') and (q, bit) not in table
        table[q, bit] = (written, 1 if direction == 'R' else -1, target)
    states = {q for q, bit in table}
    assert len(states) == 194 and 254 not in states
    assert set(table) == {(q, bit) for q in states for bit in (0, 1)}
    assert {target for written, direction, target in table.values()} - states == {254}
    return table, states


def table_text(table):
    return ''.join(f'{q} {bit} {written} {"R" if direction == 1 else "L"} {target}\n'
                   for (q, bit), (written, direction, target) in sorted(table.items()))


def canonical_dense(table, states):
    labels, seen = [74], {74}
    for q in labels:
        for bit in (0, 1):
            target = table[q, bit][2]
            if target != 254 and target not in seen:
                seen.add(target)
                labels.append(target)
    assert seen == states and len(labels) == 194
    labels.append(254)
    inverse = {q: i for i, q in enumerate(labels)}
    dense = {(inverse[q], bit): (written, direction, inverse[target])
             for (q, bit), (written, direction, target) in table.items()}
    assert {(labels[q], bit): (written, direction, labels[target])
            for (q, bit), (written, direction, target) in dense.items()} == table
    return dense, labels


def resolve(sites):
    assert isinstance(sites, list) and len(sites) == 3646
    names = {'inc': 'CI', 'dec': 'CD', 'breakTo': 'CB', 'continueTo': 'CC', 'halt': 'CH'}
    mapped = []
    for item in sites:
        assert isinstance(item, list) and len(item) == 3
        path, op, arg = item
        assert isinstance(path, str) and set(path) <= {'0', '1'} and len(path) <= 48
        assert op in names
        assert arg is None if op == 'halt' else type(arg) is int
        mapped.append([path, names[op], arg])
    assert len({path for path, op, arg in mapped}) == len(mapped)
    arithmetic, _ = source.graph_arithmetic(mapped)
    assert arithmetic == source.graph_intervals(mapped)
    opcodes = {'identity': 'jump', 'increment': 'inc', 'decrement': 'dec', 'halt': 'halt'}
    instructions = [[opcodes[effect[0]]] + effect[1:] + targets
                    for effect, targets in arithmetic]
    return mapped, instructions


def blank_start(table, seed_path):
    logical = [2] + [0] * 8
    physical = [None] * 9
    for i, j in enumerate(PHY):
        physical[j] = logical[i]
    frame = [1] + [int(bit) for bit in seed_path] + [0] * (48 - len(seed_path)) + [1]
    for value in physical + [1] * 26:
        frame.extend([0] + [1] * (value + 1))
    expected = {i - 3 for i, bit in enumerate(frame) if bit}
    ones, q, head = set(), 74, 0
    for step in range(1_000_001):
        if q == 84 and head == -2 and ones == expected:
            assert step == 57768
            return {'steps': step, 'state': q, 'head': head,
                    'ones': sorted(ones), 'source_site': 25,
                    'source_path': seed_path, 'header_base': 48,
                    'logical_registers': logical, 'physical_registers': physical,
                    'spare_values': [1] * 26, 'complete_tape_equality': True}
        assert q != 254, f'Premature blank-start halt at step {step}'
        written, direction, q = table[q, int(head in ones)]
        if written:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    raise AssertionError('Exact complete source seed not reached within startup bound')


def verify(machine=None, output=None):
    started = time.monotonic()
    machine = machine or PACKAGE / 'machines' / 'PA194R'
    output = output or HERE / 'recorded'
    out = output / 'PA194R'
    out.mkdir(parents=True, exist_ok=True)
    table, states = read_table(machine / 'machine.native.tm')
    native_bytes = table_text(table).encode()
    dense, labels = canonical_dense(table, states)
    dense_bytes = table_text(dense).encode()
    assert native_bytes == (machine / 'machine.native.tm').read_bytes()
    assert dense_bytes == (machine / 'machine.tm').read_bytes()
    assert sha(dense_bytes) == EXPECTED_DENSE_SHA

    sites = json.loads((machine / 'sites.json').read_text())
    mapped, instructions = resolve(sites)
    assert instructions == json.loads((machine / 'instructions.json').read_text())
    previous = PACKAGE / 'machines' / 'PA194F'
    prior_sites = json.loads((previous / 'sites.json').read_text())
    _, prior_instructions = resolve(prior_sites)
    assert prior_instructions == json.loads((previous / 'instructions.json').read_text())
    assert instructions == prior_instructions
    assert [s[1:] for s in sites] == [s[1:] for s in prior_sites]
    changed_paths = [i for i, (a, b) in enumerate(zip(prior_sites, sites)) if a[0] != b[0]]
    assert len(changed_paths) == 1111 and sites[25] == prior_sites[25]
    original_bytes = (PACKAGE / 'inputs' / 'pa194CS.instructions.json').read_bytes()
    assert sha(original_bytes) == 'e2f74c0fad95734738788b98e76dc3e11748c0819ad7ef2b2998f81e0140da87'
    cut = four_site_cut.verify(json.loads(original_bytes), instructions)
    write_json(out / 'four_site_cut.json', cut)
    write_json(out / 'changed_paths.json', changed_paths)
    write_json(out / 'sites.json', sites)
    write_json(out / 'instructions.json', instructions)
    write_json(out / 'labels.json', labels)
    (out / 'machine.native.tm').write_bytes(native_bytes)
    (out / 'machine.tm').write_bytes(dense_bytes)
    print('PA194R: both source resolvers agree; entire graph equals PA194F; 1,111 paths changed.', flush=True)

    mapping = {int(k): v for k, v in json.loads((HERE / 'reference' / 'legacy_mapping.json').read_text()).items()}
    for q in states | {254}:
        mapping.setdefault(q, q + 10000)
    assert len({mapping[q] for q in states | {254}}) == 195
    assert mapping[84] == 96 and mapping[254] == 254
    symbolic = {(mapping[q], bit): (written, direction, mapping[target])
                for (q, bit), (written, direction, target) in table.items()}
    runtime.PHY = PHY
    lemmas, blocks = sym.prove_blocks(symbolic)
    assert len(blocks) == 4
    write_json(out / 'list_lemmas.json', blocks)
    print('PA194R: four list lemmas rederived from literal rows.', flush=True)
    contracts, total, maximum = [], 0, 0
    for i, site in enumerate(mapped):
        for positive in ([False, True] if site[1] == 'CD' else [False]):
            result = sym.case(symbolic, lemmas, site, positive)
            total += result['symbolic_steps']
            maximum = max(maximum, result['symbolic_steps'])
            contracts.append({'site': i, 'positive': positive,
                              'duration': result['duration'], 'motion': result['motion'],
                              'symbolic_steps': result['symbolic_steps']})
        if (i + 1) % 500 == 0:
            print(f'PA194R: checked {i + 1} of {len(sites)} source sites.', flush=True)
    assert len(contracts) == 4746
    minimum_duration = min(c['duration'][0] for c in contracts)
    assert minimum_duration > 0
    encoded = (json.dumps(contracts, separators=(',', ':')) + '\n').encode()
    (out / 'contracts.json').write_bytes(encoded)
    seed = blank_start(table, sites[25][0])
    write_json(out / 'blank_seed.json', seed)
    receipt = {
        'family': 'PA194R', 'status': 'PASS',
        'working_states': 194, 'transition_rows': 388,
        'native_sha256': sha(native_bytes), 'dense_sha256': sha(dense_bytes),
        'dense_conjugacy_exact': True, 'source_sites': 3646,
        'universal_source_outcomes': 4746, 'independent_cfg_resolvers_agree': True,
        'source_instruction_graph_equal_PA194F': True,
        'source_operations_equal_PA194F': True, 'changed_source_paths': len(changed_paths),
        'four_site_zero_cut_checked': True, 'symbolic_steps': total,
        'maximum_symbolic_steps': maximum,
        'minimum_positive_duration_constant': minimum_duration,
        'four_list_lemmas_rederived_from_literal_table': True,
        'arithmetic_box_oracles': False, 'compiler_imports': False,
        'register_scope': 'Nine arbitrary natural register values; both outcomes of every decrement.',
        'spare_scope': 'Arbitrary finite nonempty list of arbitrary natural spare values.',
        'startup_steps': seed['steps'], 'whole_blank_tape_equal': True,
        'contracts_sha256': sha(encoded), 'kernel_checked': False,
        'elapsed_seconds': round(time.monotonic() - started, 3)}
    write_json(out / 'receipt.json', receipt)
    print(json.dumps(receipt, indent=2), flush=True)
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--machine', type=Path, help='Input directory (default: machines/PA194R).')
    parser.add_argument('--output', type=Path, help='Parent directory for PA194R receipts (default: verification/recorded).')
    args = parser.parse_args()
    verify(machine=args.machine, output=args.output)
