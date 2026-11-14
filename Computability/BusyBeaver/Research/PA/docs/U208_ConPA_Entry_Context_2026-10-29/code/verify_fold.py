#!/usr/bin/env python3
"""Independent finite certificate for Joint U209 -> U208.

Uses exact short predecessor arguments, not a general context-search engine.
All unspecified tape cells are symbolic and must not be read or written.
"""
import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_PARENT_SHA = 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'


def need(test, message):
    if not test:
        raise ValueError(message)


def read_table(path):
    data = path.read_bytes()
    table = {}
    starts = []
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line.split()[-1]))
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        key = int(q), int(b)
        need(key not in table, 'Duplicate transition')
        need(direction in ('L', 'R'), 'Bad direction')
        need(int(b) in (0, 1) and int(w) in (0, 1), 'Nonbinary symbol')
        need(int(q) >= 0 and int(target) >= 0, 'Negative state label')
        table[key] = int(w), -1 if direction == 'L' else 1, int(target)
    need(starts == [0], 'Start convention')
    return table, hashlib.sha256(data).hexdigest()


def incoming(table, target):
    return sorted((q, b, w, d) for (q, b), (w, d, z) in table.items()
                  if z == target)


def make_new(old):
    rho = lambda q: 211 if q == 172 else q
    new = {(q, b): (w, d, rho(z))
           for (q, b), (w, d, z) in old.items() if q != 172}
    new[211, 0] = 0, -1, 217
    return new


def check_local(old, new, old_state, bit, known_cells):
    initial = dict(known_cells)
    need(initial.get(0) == bit, 'Missing current bit')
    ow, od, oz = old[old_state, bit]
    expected = dict(initial)
    expected[0] = ow
    expected_state = 211 if oz == 172 else oz
    cells = dict(initial)
    state, head = 211, 0
    trace = []
    while len(trace) < 10:
        need(head in cells, 'Trace reads an unspecified exterior cell')
        observed = cells[head]
        w, d, z = new[state, observed]
        trace.append([state, head, observed, w, d, z])
        cells[head] = w
        head += d
        state = z
        if state == expected_state and head == od:
            need(cells == expected, 'Tape mismatch at proposed endpoint')
            return {'old_state': old_state, 'read': bit,
                    'known_cells': initial, 'old_transition': [ow, od, oz],
                    'new_steps': len(trace), 'trace': trace,
                    'arbitrary_exterior_untouched': True}
    raise ValueError('No matching endpoint')


def verify(old, new):
    # Every entry to old 172 has the suffix 1,0 to the left.
    need(incoming(old, 172) == [(116, 0, 0, 1)], '172 predecessor premise')
    need(incoming(old, 116) == [(215, 1, 1, 1)], '116 predecessor premise')
    # Every entry to old 211 reading 0 has a 1 immediately to the left.
    # On a right entry from 163/1, that bit has just been written.
    # On a left entry from 163/0, the read 0 rules out 132/1 and 199/1.
    # The remaining path is 216/1 -> 217/0 -> 163/0 -> 211.
    need(incoming(old, 211) == [(163, 0, 0, -1), (163, 1, 1, 1)],
         '211 predecessor premise')
    need(incoming(old, 163) == [(132, 1, 1, 1), (199, 1, 1, 1),
                              (217, 0, 0, 1)], '163 predecessor premise')
    need(incoming(old, 217) == [(216, 1, 1, 1)], '217 predecessor premise')
    need(0 not in (172, 116, 211, 163, 217), 'No initial-state exceptions')
    need(old[172, 0] == (0, -1, 67), 'Old 172/0')
    need(old[211, 0] == (0, 1, 157), 'Old 211/0')
    need(old[172, 1] == old[211, 1] == (1, 1, 184), 'Common read1 row')
    need(new == make_new(old), 'Unspecified candidate mutation')
    special = {(172, b) for b in (0, 1)} | {(211, 0)}
    for key, (w, d, z) in old.items():
        if key in special:
            continue
        need(new[key] == (w, d, 211 if z == 172 else z),
             'Ordinary transition correspondence')
    cases = [
        check_local(old, new, 172, 0, {-2: 1, -1: 0, 0: 0}),
        check_local(old, new, 172, 1, {0: 1}),
        check_local(old, new, 211, 0, {-1: 1, 0: 0}),
        check_local(old, new, 211, 1, {0: 1}),
    ]
    need([c['new_steps'] for c in cases] == [7, 1, 3, 1], 'Clock lengths')
    states = {q for q, b in new}
    need(len(states) == 208, 'Working state count')
    need(len(new) == 416 and set(new) == {(q, b) for q in states for b in (0, 1)},
         'Complete binary transition table')
    need({z for _, _, z in new.values()} - states == {254}, 'Halt closure')
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', type=Path, required=True,
                        help='Pinned Joint U209 native transition table')
    parser.add_argument('--new', type=Path, required=True,
                        help='Proposed U208 native transition table')
    parser.add_argument('--output', type=Path,
                        default=Path('evidence/independent_fold.json'),
                        help='Write the detailed JSON certificate here')
    args = parser.parse_args()
    old, digest = read_table(args.old)
    need(digest == EXPECTED_PARENT_SHA, 'Pinned Joint U209 table mismatch')
    new, candidate_digest = read_table(args.new)
    cases = verify(old, new)
    controls = []
    for name, table_name, key, replacement in [
        ('wrong_172_predecessor', 'old', (116, 0), (1, 1, 172)),
        ('wrong_second_172_tag', 'old', (215, 1), (0, 1, 116)),
        ('wrong_211_predecessor', 'old', (163, 1), (0, 1, 211)),
        ('wrong_163_zero_tag', 'old', (217, 0), (1, 1, 163)),
        ('wrong_deep_211_tag', 'old', (216, 1), (0, 1, 217)),
        ('wrong_helper_direction', 'new', (211, 0), (0, 1, 217)),
        ('wrong_helper_write', 'new', (211, 0), (1, -1, 217)),
        ('wrong_selector_target', 'old', (217, 1), (1, 1, 214)),
    ]:
        a, b = old.copy(), new.copy()
        if table_name == 'old':
            a[key] = replacement
            b = make_new(a)
        else:
            b[key] = replacement
        try:
            verify(a, b)
        except (ValueError, KeyError):
            controls.append({'name': name, 'rejected': True})
        else:
            raise ValueError('Negative control accepted: ' + name)
    result = {'status': 'PASS', 'parent_sha256': digest,
              'candidate_sha256': candidate_digest,
              'working_states': 208, 'transition_rows': 416,
              'cases': cases, 'negative_controls': controls,
              'invariant_source': 'Only predecessor sets of the OLD 209-state table',
              'scope': 'Local all-tape stuttering simulation; no end-to-end PA kernel proof'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'parent_sha256',
                                          'candidate_sha256', 'working_states',
                                          'transition_rows')}, indent=2))


if __name__ == '__main__':
    main()
