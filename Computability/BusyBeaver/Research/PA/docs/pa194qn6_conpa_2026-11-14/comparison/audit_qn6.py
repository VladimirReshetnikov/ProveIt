#!/usr/bin/env python3
"""Independent exact Q6->QN6 splice audit against the pinned repository.

Does not import the candidate's compiler, builder, command checker or physical
simulator. This is a finite binding certificate, not an automatic PA theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

REV = '2337ce611a26e308697ccbddb2a1636f989f01c3'
DOCS = 'Computability/BusyBeaver/Research/PA/docs/'
Q6 = DOCS + 'pa194_qradix_research_2026-11-13/machines/PA194Q6/'
N6 = DOCS + 'pa194n6_research_2026-11-13/machine/'


def parse(data):
    rows = {}
    for line in data.decode('ascii').splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        q, b, w, direction, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert b in (0, 1) and w in (0, 1) and direction in ('L', 'R')
        assert (q, b) not in rows
        rows[q, b] = (w, direction, n)
    states = {q for q, b in rows}
    assert all((q, b) in rows for q in states for b in (0, 1))
    return rows


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def imp(a, b):
    return ('I', a, b)


def check_exchange(path):
    certificate = json.loads(path.read_text())
    formulas = []
    counts = {'K': 0, 'S': 0, 'MP': 0}
    for i, line in enumerate(certificate['lines']):
        result = freeze(line['formula'])
        rule = line['rule']
        counts[rule] += 1
        if rule == 'K':
            a, b = map(freeze, line['parameters'])
            expected = imp(a, imp(b, a))
        elif rule == 'S':
            a, b, c = map(freeze, line['parameters'])
            expected = imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
        else:
            assert rule == 'MP'
            major, minor = line['major'], line['minor']
            assert 0 <= major < i and 0 <= minor < i
            assert formulas[major][0] == 'I'
            assert formulas[major][1] == formulas[minor]
            expected = formulas[major][2]
        assert result == expected
        formulas.append(result)
    assert not certificate['assumptions']
    assert certificate['conclusion_line'] == len(formulas) - 1
    assert formulas[-1] == imp(imp('P', imp('Q', 'R')), imp('Q', imp('P', 'R')))
    return {'lines': len(formulas), 'rules': counts, 'undischarged_hypotheses': 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo', type=Path)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('independent_qn6_audit.json'))
    args = parser.parse_args()
    candidate = args.candidate
    hashes = {}

    def source(path):
        data = subprocess.check_output(['git', '-C', str(args.repo), 'show', REV + ':' + path])
        hashes['repository:' + path] = hashlib.sha256(data).hexdigest()
        return data

    def local(path):
        data = (candidate / path).read_bytes()
        hashes['candidate:' + path] = hashlib.sha256(data).hexdigest()
        return data

    labels = json.loads(source(Q6 + 'labels.json'))
    old_dense = parse(source(Q6 + 'machine.tm'))
    old_native = {(labels[q], b): (w, d, labels[n] if n < len(labels) else 254)
                  for (q, b), (w, d, n) in old_dense.items()}
    new_native = parse(local('machine/machine.native.tm'))
    assert old_native.keys() == new_native.keys()
    row_changes = [(key, old_native[key], new_native[key])
                   for key in sorted(old_native) if old_native[key] != new_native[key]]
    assert row_changes == [((164, 1), (1, 'R', 98), (1, 'R', 114))]
    assert len(new_native) == 388

    old_nodes = json.loads(source(Q6 + 'nodes.json'))
    new_nodes = json.loads(local('machine/nodes.json'))
    assert old_nodes.keys() == new_nodes.keys()
    node_changes = [(key, old_nodes[key], new_nodes[key]) for key in sorted(old_nodes)
                    if old_nodes[key] != new_nodes[key]]
    assert node_changes == [('node163', ['node6', 'node55'], ['node6', 'node54'])]

    old = json.loads(source(Q6 + 'instructions.json'))
    new = json.loads(local('machine/instructions.json'))
    lo, hi = 3756, 3775

    def relocate(i):
        if i < lo:
            return i
        return lo if i < hi else i - (hi - lo)

    exterior_entries = []
    for i, row in enumerate(old):
        if lo <= i < hi:
            continue
        split = 2 if row[0] in ('inc', 'dec') else 1
        exterior_entries.extend((i, target) for target in row[split:] if lo <= target < hi)
        assert new[relocate(i)] == row[:split] + [relocate(target) for target in row[split:]]
    assert (len(old), len(new)) == (3795, 3776)
    assert exterior_entries == [(3750, 3756)]
    assert new[3756:3763] == [
        ['dec', 4, 3760, 3757], ['inc', 1, 3758], ['inc', 6, 3759],
        ['jump', 3756], ['dec', 6, 3763, 3761], ['inc', 4, 3762], ['jump', 3760]
    ]

    old_n6 = parse(source(N6 + 'unfolded202.native.tm'))
    new_raw = parse(local('machine/raw.native.tm'))
    old_fixed = {key: value for key, value in old_n6.items() if key[0] < 1300}
    new_fixed = {key: value for key, value in new_raw.items() if key[0] < 1300}
    assert old_fixed == new_fixed and len(new_fixed) == 270
    n6_instructions = json.loads(source(N6 + 'instructions.json'))
    assert len(n6_instructions) == len(new)
    instruction_changes = [(i, a, b) for i, (a, b) in enumerate(zip(n6_instructions, new)) if a != b]
    assert len(instruction_changes) == 83
    assert min(i for i, a, b in instruction_changes) == 2015
    assert max(i for i, a, b in instruction_changes) == 2133

    exchange = check_exchange(candidate / 'proof/exchange_certificate.json')
    pair = lambda a, b: (a + b) * (a + b + 1) // 2 + b
    assert pair(2, 0) == 3 and pair(0, 3) == 9
    result = {
        'status': 'PASS', 'revision': REV, 'working_states': 194,
        'Q6_to_QN6_native_row_changes': row_changes,
        'Q6_to_QN6_source_node_changes': node_changes,
        'Q6_source_sites': len(old), 'QN6_source_sites': len(new),
        'deleted_half_open_source_interval': [lo, hi],
        'sole_exterior_entry_to_deleted_interval': exterior_entries,
        'every_remaining_instruction_and_successor_exactly_relocated': True,
        'retained_copy_loop_exactly_bound': True,
        'N6_fixed_controls_unchanged': len(new_fixed) // 2,
        'resolved_Q_changes_from_N6': len(instruction_changes),
        'Q_changed_instruction_minmax_inclusive': [2015, 2133],
        'independent_exchange_certificate_replay': exchange,
        'material_command_difference_witness': {
            'store_t_w_d_h': [0, 3, 0, 0], 'command': 'MP_0',
            'stack_derivation': '3 = [U(0,0);0] = [2;0]',
            'Q6_result': [0, 9, 0, 0], 'QN6_result': [0, 3, 0, 0]
        },
        'input_sha256': hashes,
        'scope': 'Independent finite source and row binding plus flat exchange replay. Ordinary mathematical proof review and all-register physical validation are separate evidence.'
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'input_sha256'}, indent=2))


if __name__ == '__main__':
    main()
