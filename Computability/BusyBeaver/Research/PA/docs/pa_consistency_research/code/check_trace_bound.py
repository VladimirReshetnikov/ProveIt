#!/usr/bin/env python3
"""Derive an explicit trace-length bound from all accepted runtime vectors.

Standard library only.  After copying this file to a packet's code/ directory:

    python3 code/check_trace_bound.py --output certificates/trace_bound.json

The runtime proof is a prerequisite: this checker does not establish that a
recorded duration vector describes the machine.  It independently checks the
complete case census, no-overflow source conditions, canonical seed, and the
arithmetic bound implied by those vectors and the certified primitive effects.
"""

from pathlib import Path
import argparse
import gzip
import hashlib
import json


MACHINE_SHA256 = 'f6594edc95efed02f26b88f71c9b1f7699965a258739836f24e6b641887b0cd9'
SOURCE_SHA256 = 'f2fd582615c47a680c6475235139d8026bd4126b03e788e7d18c76c1ff45c49e'
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SLOTS = 13


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_conditions(rows):
    """Check every path/cut on which the certified runtime increments a PC."""
    require(len(rows) == 3812, 'Source site count')
    paths = [row[0] for row in rows]
    require(paths == sorted(set(paths)), 'Distinct canonical leaf order')
    trie = {}
    for path, op, arg in rows:
        require(path and set(path) <= {'0', '1'}, 'Binary path')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Opcode')
        require((op == 'CH' and arg is None) or
                (op != 'CH' and type(arg) is int and arg >= 0), 'Operand')
        if op in ('CI', 'CD'):
            require(arg < 9, 'Primary register range')
        if op in ('CB', 'CC'):
            require(arg >= 1, 'Positive ancestor depth')
        node = trie
        for bit in path:
            require('leaf' not in node, 'Overlapping source paths')
            node = node.setdefault(bit, {})
        require(not node, 'Duplicate or overlapping source path')
        node['leaf'] = (op, arg)

    def full(node):
        if 'leaf' in node:
            require(set(node) == {'leaf'}, 'Leaf with children')
            return
        require(set(node) == {'0', '1'}, 'Non-full source tree')
        full(node['0'])
        full(node['1'])

    full(trie)
    increments = 0
    branch_count = 0
    for path, op, arg in rows:
        branches = (False, True) if op == 'CD' else (False,)
        for positive in branches:
            branch_count += 1
            to_increment = None
            if op == 'CI' or (op == 'CD' and positive):
                to_increment = path
            elif op in ('CD', 'CB'):
                depth = 1 if op == 'CD' else arg
                positions = [i for i, bit in enumerate(path) if bit == '0']
                require(len(positions) >= depth, 'Break escapes the root')
                to_increment = path[:positions[-depth]]
            elif op == 'CC':
                require(path.count('1') >= arg, 'Continue escapes the root')
            if to_increment is not None:
                # For a fixed-width binary path, exactly an all-one word
                # (including the empty word) would wrap and shift the root.
                require(to_increment and '0' in to_increment,
                        'Incremented PC can overflow the root')
                increments += 1
    require(branch_count == 4959, 'Source branch count')
    return {'source_sites': len(rows), 'source_cases': branch_count,
            'pc_increment_cases_checked': increments,
            'pc_overflow_in_every_case': 0}


def check_seed(startup):
    require(startup['status'] == 'EXACT_BLANK_STARTUP_PASS', 'Startup status')
    require(startup['steps'] == 59164, 'Startup duration')
    require(startup['final_state'] == startup['target_state'] == 84,
            'Startup native root')
    require(startup['final_head'] == startup['target_head'] == -2,
            'Startup head')
    require(startup['final_ones'] == startup['target_ones'], 'Startup tape equality')
    logical = [2] + [0] * 8
    physical = [None] * 9
    for i, j in enumerate(PHY):
        physical[j] = logical[i]
    pc = '100000'
    gap = 48
    head = -2
    expected = {head - 1, head + gap}
    expected.update(head + i for i, bit in enumerate(pc) if bit == '1')
    pos = head + gap + 1
    for value in physical + [1] * 26:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    require(set(startup['final_ones']) == expected, 'Canonical complete seed tape')
    return {'startup_steps': 59164, 'initial_gap': 48,
            'initial_register_sum': 2, 'initial_spares': 26,
            'first_spare_value': 1, 'initial_remaining_spare_width': 25 * 3}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--packet', type=Path,
                   default=Path(__file__).resolve().parents[1])
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    root = args.packet.resolve()
    machine = root / 'data/variant196.native.tm'
    source = root / 'data/variant196_source.json'
    cases_path = root / 'certificates/variant196/runtime_cases.json.gz'
    runtime_path = root / 'certificates/variant196/runtime.json'
    startup_path = root / 'certificates/variant196/startup.json'
    require(sha(machine) == MACHINE_SHA256, 'Machine identity')
    require(sha(source) == SOURCE_SHA256, 'Source identity')
    runtime = json.loads(runtime_path.read_text())
    startup = json.loads(startup_path.read_text())
    cases = json.loads(gzip.decompress(cases_path.read_bytes()))
    rows = json.loads(source.read_text())
    require(runtime['status'] == 'FULL_UNIVERSAL_RUNTIME_PASS', 'Runtime status')
    require(runtime['machine_sha256'] == startup['machine_sha256'] == MACHINE_SHA256,
            'Machine receipt identities')
    require(runtime['source_sha256'] == SOURCE_SHA256, 'Source receipt identity')
    require(runtime['header_base'] == 48 and runtime['expected_states'] == 196,
            'Runtime convention')
    conditions = source_conditions(rows)
    seed = check_seed(startup)
    require(rows[25][0] == '100000', 'Initial source path')
    expected_cases = {(i, positive) for i, row in enumerate(rows)
                      for positive in ((False, True) if row[1] == 'CD' else (False,))}
    found_cases = {(case['site_index'], case['positive']) for case in cases}
    require(len(cases) == len(found_cases) == 4959 and found_cases == expected_cases,
            'Missing, duplicate, or unexpected instruction case')
    require(runtime['cases'] == len(cases), 'Runtime receipt case count')

    bounds = []
    for case in cases:
        d = case['duration']
        require(len(d) == SLOTS and all(type(x) is int and x >= 0 for x in d)
                and d[0] > 0, 'Nonpositive or malformed duration')
        _, op, arg = rows[case['site_index']]
        if op == 'CD' and not case['positive']:
            # This branch has tested register = 0. Its allocated affine
            # variable is unused, and therefore must not enter the clock.
            require(d[2 + arg] == 0, 'Zero-decrement duration uses an absent parameter')
        # d = [constant, gap excess, nine primary parameters, first spare,
        #      remaining spare-list width].  In a positive CD branch its
        # tested primary parameter is the register value minus one, which
        # only improves the sum bound below.
        m = max(d[2:11])
        constant = d[0] + 2 * m + d[11] + 75 * d[12]
        slope = d[1] + m + 3 * d[12]
        bounds.append({'site_index': case['site_index'], 'positive': case['positive'],
                       'duration': d, 'constant': constant, 'slope': slope})
    largest_constant = max(bounds, key=lambda b: b['constant'])
    largest_slope = max(bounds, key=lambda b: b['slope'])
    require(largest_constant['constant'] == 700, 'Unexpected global constant')
    require(largest_slope['slope'] == 18, 'Unexpected global slope')
    require(all(b['constant'] <= 700 and b['slope'] <= 18 for b in bounds),
            'Uniform affine bound')
    require(sum(c['symbolic_steps'] for c in cases) == runtime['symbolic_inferences'] == 1177411,
            'Runtime inference census')
    # The summation is an exact polynomial identity, not an additional
    # finite numerical regression: sum_{n<T} n = T(T-1)/2 in PA.
    require(18 % 2 == 0, 'Integral quadratic coefficient')
    report = {
        'status': 'TRACE_BOUND_PASS',
        'machine_sha256': sha(machine), 'source_sha256': sha(source),
        'runtime_cases_sha256': sha(cases_path),
        'source_conditions': conditions, 'seed': seed,
        'checked_duration_vectors': len(cases),
        'coordinatewise_maximum_duration': [max(c['duration'][i] for c in cases)
                                             for i in range(SLOTS)],
        'maximum_constant_witness': largest_constant,
        'maximum_slope_witness': largest_slope,
        'inductive_invariants_at_live_boundaries_after_n_source_steps': {
            'gap_excess_over_48': '<= n',
            'sum_of_nine_primary_values': '<= n + 2',
            'first_spare_value': '= 1',
            'remaining_spare_list_width': '<= 75 + 3*n',
            'justification': 'Each CI raises the primary sum by one and appends B(1), width three; '
                             'a positive CD lowers that sum by one and increases the gap by one; '
                             'other live branches preserve these quantities. The first spare is '
                             'preserved in every certified contract, and no PC increment overflows.'},
        'per_source_step_bound': '700 + 18*n',
        'T_source_steps_including_startup_bound': '59164 + 700*T + 9*T*(T-1)',
        'prefix_convention': 'A live prefix, or a prefix whose final primitive instruction halts; '
                             'absorbing coded-halt self-loops are not additional primitive instructions.',
        'scope': 'Arithmetic bound derived from every recorded duration and the certified primitive '
                 'effects. Validity of those uniform runtime contracts remains a prerequisite; '
                 'this is not a fresh runtime proof, a nonhalting test, or a proof-assistant certificate.'
    }
    encoded = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
