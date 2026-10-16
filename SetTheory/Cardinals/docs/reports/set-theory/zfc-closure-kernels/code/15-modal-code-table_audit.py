#!/usr/bin/env python3
"""Standalone stdlib audit of the two delivered numeric Turing machines.

Checks pinned bytes, table conventions, graph reachability, exact refinement,
and a literal one-million-step blank prefix. No external source is needed.
This does not identify the AX entry, prove a future invariant, or establish
a compiler simulation or consistency calibration.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

if sys.flags.optimize:
    raise SystemExit('table_audit.py requires ordinary Python; do not use -O or -OO.')

ROOT = Path(__file__).resolve().parents[1]
STEPS = 1_000_000
EXPECTED = (
    {'name': '250-oldrho6', 'states': 250, 'rounds': 12,
     'sha256': '2bc151a7ba41fab11a2ebf15c7c9913acf46241843ec12e4bec48417153d8cd0'},
    {'name': '249-dual', 'states': 249, 'rounds': 11,
     'sha256': '711d6edf4a523db3d8861387636dbc8fc028eb74a7f4d3f174060a128d04a3a9'},
)
EXPECTED_PREFIX = {
    'requested_steps': STEPS, 'executed_steps': STEPS, 'halted': False,
    'final_state': 24, 'final_head': 248, 'final_ones': 223,
    'final_configuration_sha256':
        'fbe8133c0bdf91b636fb874702396caf107525c3f0b906ce2b4e5e43c94c49db',
    'observed_states': 133, 'observed_transition_pairs': 253,
    'finite_prefix_only': True,
    'does_not_establish_future_read_or_marker_invariants': True,
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse_table(data, count):
    rows, start = {}, None
    for line_number, raw in enumerate(data.decode('utf-8').splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith('#!'):
            match = re.fullmatch(r'#!\s+start\s+([0-9]+)', line)
            require(match is not None and start is None,
                    f'Line {line_number}: invalid or repeated start directive')
            start = int(match[1])
            continue
        if line.startswith('#'):
            continue
        match = re.fullmatch(r'([0-9]+)\s+([01])\s+([01])\s+([LR])\s+([0-9]+)', line)
        require(match is not None, f'Line {line_number}: invalid binary transition')
        state, read, write, move, target = match.groups()
        key = int(state), int(read)
        require(key not in rows, f'Line {line_number}: duplicate transition')
        rows[key] = int(write), 1 if move == 'R' else -1, int(target)
    require(start == 0, 'Expected exactly one start directive with state 0')
    require(set(rows) == {(q, b) for q in range(count) for b in (0, 1)},
            'Expected contiguous working states 0..n-1 with two binary rows each')
    require({t for _, _, t in rows.values()} - set(range(count)) == {count},
            'Expected n to be the sole referenced terminal state')
    return rows


def graph_reachability(rows, halt):
    reached, pending = {0}, [0]
    while pending:
        state = pending.pop()
        if state == halt:
            continue
        for bit in (0, 1):
            target = rows[state, bit][2]
            if target not in reached:
                reached.add(target)
                pending.append(target)
    return reached


def exact_refinement(rows, halt):
    """Separate halt initially, then refine both write/move/target signatures."""
    classes = {q: int(q == halt) for q in range(halt + 1)}
    rounds = 0
    while True:
        signatures, refined = {}, {}
        for q in range(halt + 1):
            key = ('halt',) if q == halt else tuple(
                (rows[q, b][0], rows[q, b][1], classes[rows[q, b][2]]) for b in (0, 1))
            refined[q] = signatures.setdefault(key, len(signatures))
        rounds += 1
        stable = len(set(refined.values())) == len(set(classes.values()))
        classes = refined
        if stable:
            return len(set(classes.values())) - 1, rounds


def simulate_blank(rows, halt):
    ones, observed = set(), {}
    state, head, steps = 0, 0, 0
    while steps < STEPS and state != halt:
        read = int(head in ones)
        observed[state] = observed.get(state, 0) | (1 << read)
        write, move, target = rows[state, read]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        state = target
        steps += 1
    configuration = {'state': state, 'head': head, 'one_cells': sorted(ones)}
    encoded = json.dumps(configuration, sort_keys=True, separators=(',', ':')).encode('utf-8')
    return {
        'requested_steps': STEPS, 'executed_steps': steps, 'halted': state == halt,
        'final_state': state, 'final_head': head, 'final_ones': len(ones),
        'final_configuration_sha256': hashlib.sha256(encoded).hexdigest(),
        'observed_states': len(observed),
        'observed_transition_pairs': sum(mask.bit_count() for mask in observed.values()),
        'finite_prefix_only': True,
        'does_not_establish_future_read_or_marker_invariants': True,
    }


def audit_one(directory, expected):
    filename = 'machine-' + expected['name'] + '.tm'
    data = (directory / filename).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    require(digest == expected['sha256'], filename + ': table digest mismatch')
    count = expected['states']
    rows = parse_table(data, count)
    require(graph_reachability(rows, count) == set(range(count + 1)),
            'Some working or halt states are graph-unreachable')
    classes, rounds = exact_refinement(rows, count)
    require(classes == count, 'Expected singleton exact working-state classes')
    require(rounds == expected['rounds'], 'Unexpected exact-refinement round count')
    halt_edges = sum(target == count for _, _, target in rows.values())
    require(halt_edges == 2, 'Expected exactly two halting edges')
    prefix = simulate_blank(rows, count)
    require(prefix == EXPECTED_PREFIX, 'Blank prefix differs from the pinned endpoint')
    previous = json.loads((directory / ('audit-' + expected['name'] + '.json')).read_text())
    require(previous['prefix'] == prefix, 'Prefix differs from delivered audit JSON')
    require(previous['normalization']['numeric_table_sha256'] == digest,
            'Digest differs from delivered audit JSON')
    require(previous['graph_reachable_working_states'] == count and
            previous['bisimulation_working_classes'] == classes and
            previous['refinement_rounds'] == rounds,
            'Finite table facts differ from delivered audit JSON')
    return {
        'filename': filename, 'sha256': digest, 'start_state': 0, 'halt_state': count,
        'working_states': count, 'complete_binary_rows': len(rows),
        'halt_edges': halt_edges, 'graph_reachable_working_states': count,
        'bisimulation_working_classes': classes, 'refinement_rounds': rounds,
        'prefix': prefix, 'existing_audit_JSON_matches': True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--machines-dir', type=Path, default=ROOT / 'machines')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {
        'checker': 'standalone numeric-table audit, standard library only',
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'candidates': [audit_one(args.machines_dir, expected) for expected in EXPECTED],
        'configuration_digest_format':
            'SHA-256 of UTF-8 JSON with sorted keys and no spaces; keys state, head, '
            'one_cells (sorted integer positions).',
        'AX_nonentry_checked_by_this_numeric_audit': False,
        'AX_nonentry_scope':
            'Numeric tables contain no routine-entry metadata. The report\'s AX nonentry '
            'statement is inherited from source trace evidence, not checked here.',
        'scope':
            'Finite table facts and one-million-step prefixes only. No future invariant, '
            'compiler simulation, consistency calibration, unbounded nonhalting proof, '
            'or general minimality theorem is established.',
    }
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
