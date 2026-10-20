#!/usr/bin/env python3
"""Independent whole-tape replay of archived ray witnesses and startup control."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        assert b in (0, 1) and w in (0, 1) and direction in ('L', 'R')
        assert (q, b) not in table
        table[q, b] = (w, 1 if direction == 'R' else -1, target)
    states = {q for q, _ in table}
    assert 254 not in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert all(z in states or z == 254 for _, _, z in table.values())
    return table, states


def replay(table, start, steps):
    state, head, ones = start, 0, set()
    trace = []
    for tick in range(steps):
        bit = int(head in ones)
        write, move, target = table[state, bit]
        trace.append([tick, state, head, bit, write, move, target])
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        state, head = target, head + move
    return state, head, ones, trace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--baseline', type=Path,
                        default=ROOT.parent.parent / 'candidate-k218/k218.native.tm')
    args = parser.parse_args()
    assert not args.output.exists(), 'Choose a fresh output file'
    baseline_bytes = args.baseline.read_bytes()
    assert hashlib.sha256(baseline_bytes).hexdigest() == \
        '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
    baseline, old_states = read_table(args.baseline)
    table, states = read_table(ROOT / 'core217.native.tm')
    expected = dict(baseline)
    del expected[301, 0], expected[301, 1]
    expected.update({(87, 0): (0, 1, 88), (88, 0): (0, -1, 51),
                     (51, 0): (0, 1, 122)})
    assert table == expected and len(old_states) == 218
    assert states == old_states - {301} and len(states) == 217
    archived = json.loads((ROOT / 'verification.json').read_text())
    witnesses = archived['proofs']
    assert len(witnesses) == 217 and {w['start'] for w in witnesses} == states
    historical = json.loads((ROOT / 'start0-historical-prefix.json').read_text())
    for witness in witnesses:
        q, h, ones, trace = replay(table, witness['start'], witness['prefix_steps'])
        assert (q, h, sorted(ones)) == (witness['state'], witness['head'], witness['ones'])
        assert h not in ones and list(table[q, 0]) == witness['ray_action']
        write, direction, target = table[q, 0]
        assert target == q and q != 254
        assert all(x < h if direction == 1 else x > h for x in ones)
        if witness['start'] == 0:
            assert trace == historical['finite_trace']
    control = json.loads((ROOT / 'control.jsonl').read_text())
    assert control['status'] == 'ACCEPTED_SEED_FRAME' and control['start'] == 0
    assert len(control['observations']) == 1
    frame = control['observations'][0]
    assert frame['steps'] == 312909
    q, h, ones, _ = replay(baseline, 0, frame['steps'])
    assert (q, h, sorted(ones)) == (84, -5, frame['ones'])
    # Independently encode the required logical seed as the complete support.
    logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
    physical = [0] * 9
    for value, position in zip(logical, [6, 2, 0, 4, 3, 7, 8, 5, 1]):
        physical[position] = value
    support, position = {-6, 139}, 140
    for value in physical + [1] * 130:
        support.update(range(position + 1, position + value + 2))
        position += value + 2
    assert ones == support and len(ones) == 277
    assert frame['logical'] == logical and frame['spares'] == [1] * 130
    assert frame['gap'] == 80
    result = {
        'status': 'ALL_START_RAYS_AND_ACCEPTED_STARTUP_CONTROL_REPLAY_PASS',
        'working_starts': 217, 'complete_tape_prefixes': 217,
        'ray_prefix_transitions': sum(w['prefix_steps'] for w in witnesses),
        'control_steps': 312909, 'control_ones': 277,
        'scope': 'This exact 217-row-state table, blank tape, any working start; '
                 'no assertion about further table changes or other initial tapes.',
        'ray_induction': 'A zero-reading self-loop moves into a blank half-line; '
                         'every write remains behind the head, so the same nonhalting '
                         'row executes forever.',
        'review_role': 'Independent Python implementation by the discovery author; '
                       'no external peer or proof-assistant execution claimed.',
        'inputs': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                   [args.baseline, ROOT / 'core217.native.tm', ROOT / 'verification.json',
                    ROOT / 'control.jsonl', ROOT / 'start0-historical-prefix.json',
                    Path(__file__).resolve()]}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'inputs'}, indent=2))


if __name__ == '__main__':
    main()
