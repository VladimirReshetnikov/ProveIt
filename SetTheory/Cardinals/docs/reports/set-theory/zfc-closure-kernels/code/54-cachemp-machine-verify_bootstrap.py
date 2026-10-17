#!/usr/bin/env python3
"""Self-contained finite verification of the 252-state cache-MP discovery.

Uses Python's standard library only. Reconstructs the changed table from the
pinned input, checks all 504 canonical row conjugacies, verifies equality of
all 55 inherited register-box support rows, and simulates the complete actual
707393-transition blank prefix twice: once with an unbounded set tape and
once with an independently coded integer-bitvector tape and canonical states.

This is a finite arithmetic verification. The unbounded source-to-machine
simulation and the consistency equivalence are separate mathematical proofs.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

SOURCE_SHA = '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
OLD_SHA = '9ba862d15e0f689525281e1c96083acf7f389157bd56d6a2676f223106dc07a9'
RHO = [0, 3, 5, 6, 8, 7, 4, 2, 1]
PREVIOUS_PHYSICAL = [6, 2, 0, 4, 3, 7, 8, 5, 1]
PHYSICAL = [4, 5, 0, 8, 6, 2, 1, 7, 3]
SKIP = [60, 44, 31, 56, 38, 40, 28, 64, 69]
SELECTORS = {(169, 1), (173, 1), (18, 1), (201, 1), (21, 1),
             (25, 1), (39, 1), (47, 1), (49, 1), (53, 1),
             (65, 1), (70, 1), (72, 1), (93, 1)}
BOX_STATES = {0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56,
              59, 60, 63, 64, 69, 73, 75, 83, 85, 95, 97, 109, 112, 131}
BOX_ROWS = {(q, b) for q in BOX_STATES for b in (0, 1)} - {(3, 0)}
BOOT_STEPS = 707393
PRIMARY = [0, 0, 0, 0, 6, 0, 2, 0, 0]
SPARES = [0] * 295


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def parse(raw, halt):
    rows = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, t = line.split()
        require(b in ('0', '1') and w in ('0', '1') and d in ('L', 'R'),
                'invalid binary transition')
        key = int(q), int(b)
        require(key not in rows, 'duplicate transition')
        rows[key] = int(w), d, int(t)
    states = {q for q, b in rows}
    require(len(rows) == 2 * len(states), 'incomplete transition table')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'missing row')
    require(halt not in states, 'halt must be a separate target')
    require(all(t in states or t == halt for w, d, t in rows.values()), 'unknown target')
    return rows


def encode(rows, start=0):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {d} {t}\n'
        for (q, b), (w, d, t) in sorted(rows.items()))).encode('ascii')


def repaint(head, gap, values):
    ones = {head - 1, head + gap}
    cursor = head + gap + 1
    for value in values:
        require(value >= 0, 'negative unary register')
        cursor += 1
        ones.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    return ones


def simulate_set(rows):
    state, head, ones = 0, 0, set()
    leftmost = rightmost = 0
    used = Counter()
    for step in range(BOOT_STEPS):
        require(state != 254, f'old-label machine halted during prefix at {step}')
        read = int(head in ones)
        key = state, read
        used[key] += 1
        write, movement, following = rows[key]
        if write == 1:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if movement == 'R' else -1
        state = following
        leftmost, rightmost = min(leftmost, head), max(rightmost, head)
    return state, head, ones, leftmost, rightmost, used


def simulate_integer(rows, leftmost, rightmost):
    # Different representation, state labels, transition storage, and loop.
    zero = [rows[q, 0] for q in range(252)]
    one = [rows[q, 1] for q in range(252)]
    q, position, tape, remaining = 0, 0, 0, BOOT_STEPS
    while remaining:
        require(0 <= q < 252, 'canonical machine halted before the endpoint')
        require(leftmost <= position <= rightmost, 'bitvector run left the checked interval')
        mask = 1 << (position - leftmost)
        instruction = one[q] if tape & mask else zero[q]
        if instruction[0]:
            tape |= mask
        else:
            tape &= ~mask
        if instruction[1] == 'L':
            position -= 1
        else:
            position += 1
        q = instruction[2]
        remaining -= 1
    positions = set()
    while tape:
        smallest = tape & -tape
        positions.add(leftmost + smallest.bit_length() - 1)
        tape ^= smallest
    return q, position, positions


def graph_reachable(rows, initial):
    seen, pending = set(), [initial]
    while pending:
        q = pending.pop()
        if q == 254 or q in seen:
            continue
        seen.add(q)
        pending.extend(rows[q, b][2] for b in (0, 1))
    return seen


def verify(directory):
    source_raw = (directory / 'permutation252_source_old.tm').read_bytes()
    old_raw = (directory / 'cache_mp252_old.tm').read_bytes()
    canonical_raw = (directory / 'cache_mp252.tm').read_bytes()
    renumber = json.loads((directory / 'renumbering.json').read_text())
    boot = json.loads((directory / 'bootstrap.json').read_text())
    audit = json.loads((directory / 'row_audit.json').read_text())
    graph = json.loads((directory / 'graph_audit.json').read_text())
    require(sha(source_raw) == SOURCE_SHA, 'pinned source artifact hash mismatch')
    require(sha(old_raw) == OLD_SHA, 'positive old-label artifact hash mismatch')
    source = parse(source_raw, 254)
    old = parse(old_raw, 254)
    canonical = parse(canonical_raw, 252)
    expected_old = dict(source)
    require(expected_old[204, 1] == (1, 'R', 113), 'wrong MP source action')
    expected_old[204, 1] = 1, 'R', 151
    for key in SELECTORS:
        w, d, t = expected_old[key]
        require((w, d) == (0, 'R') and t in SKIP, 'wrong selector source action')
        expected_old[key] = w, d, SKIP[RHO[SKIP.index(t)]]
    require(encode(expected_old) == old_raw, 'explicit fourteen-row construction mismatch')
    states = [q for q in range(254) if q not in (5, 8)]
    require(sorted({q for q, b in old}) == states, 'wrong old working state set')
    require(sorted({q for q, b in canonical}) == list(range(252)), 'wrong canonical state set')
    mapping = {q: i for i, q in enumerate(states)} | {254: 252}
    expected = {(mapping[q], b): (w, d, mapping[t])
                for (q, b), (w, d, t) in old.items()}
    require(encode(expected) == canonical_raw, 'row-by-row canonical conjugacy mismatch')
    require(renumber['old_to_canonical'] == [[q, mapping[q]] for q in states + [254]], 'forward map mismatch')
    require(renumber['canonical_to_old'] == states + [254], 'inverse map mismatch')
    require(renumber['old_start'] == renumber['canonical_start'] == 0, 'actual start was changed')
    require((renumber['old_halt'], renumber['canonical_halt']) == (254, 252), 'halt labels mismatch')
    require(renumber['logical_to_physical'] == PHYSICAL == [RHO[p] for p in PREVIOUS_PHYSICAL], 'physical map mismatch')
    require(renumber['source_sha256'] == SOURCE_SHA and renumber['old_sha256'] == OLD_SHA and
            renumber['canonical_sha256'] == sha(canonical_raw), 'renumbering hashes mismatch')
    require(len(BOX_ROWS) == 55 and all(source[k] == old[k] for k in BOX_ROWS), 'inherited box row changed')
    require(audit['box_support_rows'] == [list(k) + list(source[k]) for k in sorted(BOX_ROWS)], 'box support list mismatch')
    changed = {k for k in source if source[k] != old[k]}
    require(len(changed) == 14 and (204, 1) in changed and changed - {(204, 1)} <= SELECTORS, 'changed row set mismatch')
    require({(r['old_state'], r['read']) for r in audit['changes']} == changed, 'row audit change set mismatch')
    for row in audit['changes']:
        key = row['old_state'], row['read']
        require(row['source_action'] == list(source[key]) and row['new_old_action'] == list(old[key]), 'row audit action mismatch')
        require(row['new_canonical_action'] == list(canonical[mapping[key[0]], key[1]]), 'canonical action audit mismatch')
    halt_rows = [list(k) + list(v) for k, v in canonical.items() if v[2] == 252]
    require(halt_rows == [[75, 1, 1, 'R', 252]], 'final halt write or movement changed')
    expected_ones = repaint(-13, 40, PRIMARY + SPARES)
    require((boot['steps'], boot['state'], boot['head'], boot['gap']) == (707393, 94, -13, 40), 'wrong bootstrap endpoint')
    require(boot['start_state'] == 0 and boot['start_head'] == 0 and boot['start_one_positions'] == [], 'nonblank initial configuration')
    require(boot['physical_primary'] == PRIMARY and boot['spare_values'] == SPARES, 'register frame mismatch')
    logical = [PRIMARY[p] for p in PHYSICAL]
    require(boot['logical_primary'] == logical == [6, 0, 0, 0, 2, 0, 0, 0, 0], 'logical frame mismatch')
    require(boot['one_positions'] == sorted(expected_ones) and boot['one_count'] == 314, 'whole tape certificate mismatch')
    require(boot['safe_certificate'] == {'top': ['truth'], 'cache': ['truth'], 'stack': []}, 'wrong Safe certificate')
    require(logical[1] == logical[2] == logical[5] == 0, 'trivial Safe hypotheses not satisfied')
    state, head, ones, leftmost, rightmost, used = simulate_set(old)
    require((state, head, ones) == (96, -13, expected_ones), 'literal unbounded set-tape replay disagrees')
    q, position, bits = simulate_integer(canonical, leftmost, rightmost)
    require((q, position, bits) == (94, -13, expected_ones), 'independent canonical bitvector replay disagrees')
    reachable = [[q, len(graph_reachable(old, q))] for q in states]
    require(graph['reachable_working_states_from_each_start'] == reachable, 'all-start graph audit mismatch')
    require(all(count == 252 for q, count in reachable), 'graph reachability assertion failed')
    partition = dict.fromkeys(states, 0)
    counts = [1]
    while True:
        signatures, refined = {}, {}
        for state in states:
            signature = tuple((w, d, -1 if t == 254 else partition[t])
                              for w, d, t in (old[state, 0], old[state, 1]))
            refined[state] = signatures.setdefault(signature, len(signatures))
        counts.append(len(signatures))
        if refined == partition:
            break
        partition = refined
    require(graph['exact_bisimulation_refinement_class_counts'] == counts, 'bisimulation refinement mismatch')
    require(counts[-1] == 252 and graph['nontrivial_exact_bisimulation_classes'] == [], 'bisimulation class assertion failed')
    for alt in graph['alternative_blank_prefixes_to_same_normalized_configuration']:
        q, h, cells = alt['old_start'], 0, set()
        for _ in range(alt['prefix_steps']):
            require(q != 254, 'alternative start halted')
            w, d, following = old[q, int(h in cells)]
            if w:
                cells.add(h)
            else:
                cells.discard(h)
            h += 1 if d == 'R' else -1
            q = following
        require(q == 1 and h == alt['head_translation'] and cells == {h + 1}, 'alternative prefix mismatch')
    return {
        'status': 'all finite checks passed',
        'scope': 'Exact table construction, canonical renaming, inherited box-row equality, finite actual blank bootstrap, whole tape frame, and graph checks; no local Lean or Coq build is claimed',
        'source_sha256': SOURCE_SHA, 'old_sha256': OLD_SHA,
        'canonical_sha256': sha(canonical_raw),
        'working_states': 252, 'transitions': 504, 'actual_start': 0,
        'canonical_halt': 252, 'canonical_halting_action': halt_rows[0],
        'box_support_rows_unchanged': 55, 'changed_rows': 14,
        'blank_steps_each_replay': BOOT_STEPS, 'independent_literal_replays': 2,
        'canonical_endpoint_state': 94, 'endpoint_head': -13,
        'logical_primary': logical, 'spare_count': 295, 'all_spares_zero': True,
        'whole_one_count': len(ones), 'whole_tape_frame_equal': True,
        'head_interval_during_prefix': [leftmost, rightmost],
        'distinct_transition_rows_used_during_prefix': len(used),
        'unlabeled_graph_reachable_working_states_from_every_start': 252,
        'exact_bisimulation_classes': counts[-1],
        'verified_alternative_blank_prefixes': len(graph['alternative_blank_prefixes_to_same_normalized_configuration']),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.directory)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
