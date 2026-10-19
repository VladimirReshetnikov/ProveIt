#!/usr/bin/env python3
"""Verify the K228 -> K227 context split fold on arbitrary binary tapes.

The input basis is the K228 table after the closed right184/181 rotation.
This checker is independent of the source tree and of bounded runtime tests.
All comparisons use explicit exceptions, so Python optimization cannot disable
checks. Python3.10+ standard library only.

Usage:
  python3 verify_split_fold.py --basis basis228_rotated_old.tm \
      --candidate k227_old.tm --output split_fold_certificate.json
"""
import argparse
import hashlib
import json
from pathlib import Path

START, HALT = 95, 254
SPECIAL = {179, 218, 242}
TAGGED = {179: 0, 242: 1}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_table(data):
    rows, starts = {}, []
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require((q, b) not in rows, 'Repeated transition row')
            require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'),
                    'Malformed transition row')
            rows[q, b] = (w, 1 if d == 'R' else -1, z)
    states = {q for q, b in rows}
    require(starts == [START], 'Unexpected starting state')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)},
            'Partial transition function')
    require({z for w, d, z in rows.values()} - states == {HALT},
            'Unexpected halting state')
    return rows


def simulate_block(table, state, left_bit, read_bit, steps):
    """A two-cell symbolic cylinder: every other tape cell is unspecified."""
    tape = {-1: left_bit, 0: read_bit}
    head, trace = 0, []
    require(steps > 0, 'Empty block')
    for _ in range(steps):
        require(state != HALT, 'Block halts internally')
        require(head in tape, 'Block reads outside the two known cells')
        scanned = tape[head]
        written, direction, target = table[state, scanned]
        trace.append(dict(state=state, head=head, read=scanned,
                          write=written, move=direction, target=target))
        tape[head] = written
        state, head = target, head + direction
    return state, head, tape, trace


def mapped_state(state, left_bit):
    return (242 if left_bit == 0 else 179) if state == 218 else state


def verify(basis_raw, candidate_raw):
    old, new = read_table(basis_raw), read_table(candidate_raw)
    old_states = {q for q, b in old}
    new_states = {q for q, b in new}
    require(len(old_states) == 228 and len(new_states) == 227,
            'Expected a228-state basis and227-state candidate')
    require(new_states == old_states - {218}, 'Wrong deleted state')
    require(START not in SPECIAL, 'Initial configuration needs a tag invariant')

    incoming = {
        q: [dict(row=[p, b], write=w, move=d)
            for (p, b), (w, d, target) in sorted(old.items()) if target == q]
        for q in sorted(SPECIAL)
    }
    # This is an induction over all runs from state95 on every binary tape.
    # Each arrival writes the claimed bit and moves right over it.
    for q, tag in TAGGED.items():
        require(incoming[q], 'Vacuous tag used in proof')
        require(all((r['write'], r['move']) == (tag, 1)
                    for r in incoming[q]), 'Inductive left-bit fact fails')
    require(all(r['move'] == 1 for r in incoming[218]),
            'Cannot classify an old218 arrival by its written bit')
    require({tuple(r['row']) for r in incoming[218]} ==
            {(187, 1), (220, 1), (237, 0)}, 'Unexpected218 predecessors')

    ordinary_count, redirected = 0, []
    for (q, b), (w, d, target) in sorted(old.items()):
        if q in SPECIAL:
            continue
        expected_target = mapped_state(target, w) if target == 218 else target
        require(new[q, b] == (w, d, expected_target),
                f'Ordinary transition fails at{q}/{b}')
        ordinary_count += 1
        if target == 218:
            require(d == 1, 'Tag redirection is not a rightward arrival')
            redirected.append(dict(row=[q, b], written_tag=w,
                                   old_target=target, new_target=expected_target))
    require(ordinary_count == 450, 'Wrong ordinary-row census')

    # (old state, left bit, scanned bit, old transitions, new transitions).
    # The old218/read0 block includes its two-cell branch at states86,98/99.
    specifications = [
        (179, 0, 0, 1, 1), (179, 0, 1, 1, 5),
        (242, 1, 0, 1, 3), (242, 1, 1, 1, 3),
        (218, 0, 0, 3, 3), (218, 0, 1, 1, 3),
        (218, 1, 0, 3, 1), (218, 1, 1, 1, 3),
    ]
    cases = []
    require({(q, tag, b) for q, tag, b, _, _ in specifications} ==
            {(q, tag, b) for q in SPECIAL for tag in (0, 1) for b in (0, 1)
             if q not in TAGGED or tag == TAGGED[q]}, 'Incomplete case split')
    for q, tag, b, old_steps, new_steps in specifications:
        old_end = simulate_block(old, q, tag, b, old_steps)
        new_q = mapped_state(q, tag)
        new_end = simulate_block(new, new_q, tag, b, new_steps)
        require(old_end[:3] == new_end[:3], 'Macro endpoint differs')
        require(old_end[0] not in SPECIAL and old_end[0] != HALT,
                'Macro endpoint needs an additional correspondence case')
        require(old_end[1] == 1 and old_end[2] == {-1: tag, 0: b},
                'Macro does not restore the original tape and advance one cell')
        cases.append(dict(old_state=q, new_state=new_q, left_bit=tag,
                          read_bit=b, old_steps=old_steps, new_steps=new_steps,
                          old_trace=old_end[3], new_trace=new_end[3],
                          endpoint=dict(state=old_end[0], head=old_end[1],
                                        unchanged_cells=[-1, 0]),
                          status='EXACT_TWO_CELL_MACRO_PASS'))

    return dict(
        format='k227-context-split-fold-certificate-v1',
        status='ALL_TAPE_STUTTERING_EQUIVALENCE_PASS',
        basis_sha256=sha(basis_raw), candidate_sha256=sha(candidate_raw),
        old_working_states=228, new_working_states=227,
        start_state=START, halt_state=HALT, deleted_state=218,
        configuration_map='218 maps to242 on left0 and179 on left1; all other states, heads and tapes are unchanged',
        inductive_old_left_bit_facts={str(q): tag for q, tag in TAGGED.items()},
        incoming_inventory=incoming, ordinary_rows_checked=ordinary_count,
        incoming_rows_redirected=redirected, exhaustive_macro_cases=len(cases),
        minimum_block_steps=1, maximum_old_block_steps=3,
        maximum_new_block_steps=5, cases=cases,
        theorem_scope=('From the common initial state95, for every binary tape '
                       'and head position, the rotated228 basis halts iff the '
                       '227 candidate halts. Two-cell macro matching is exact '
                       'for every unspecified tape exterior. All synchronization '
                       'blocks have positive bounded lengths and no internal '
                       'halting state, so divergence is preserved both ways.'),
        separation=('This proves only the binary-table split fold. Preservation '
                    'of the source rotation and source-runtime correspondence '
                    'are certified separately.'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--basis', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    certificate = verify(args.basis.read_bytes(), args.candidate.read_bytes())
    if args.output:
        args.output.write_text(json.dumps(certificate, indent=2) + '\n')
    print(json.dumps({k: certificate[k] for k in
                      ('status', 'basis_sha256', 'candidate_sha256',
                       'ordinary_rows_checked', 'exhaustive_macro_cases')}, indent=2))


if __name__ == '__main__':
    main()
