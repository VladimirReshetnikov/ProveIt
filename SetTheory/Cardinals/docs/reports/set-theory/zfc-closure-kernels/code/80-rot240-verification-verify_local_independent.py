"""Finite local certificate for the 241(rotated)-to-240 state fold.

The finite enumeration is a proof over arbitrary complete binary tapes:
all reads/writes and every guard lookup must remain in [-2,2].
A positive block joins one old step, with equal head and whole finite tape,
and all exterior cells remain untouched. The old invariant is inductive.
"""
from pathlib import Path
import argparse, collections, hashlib, itertools, json, sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run with assertions enabled; -O is not accepted')
DEFAULT_ROOT = Path(__file__).resolve().parents[1]
OLD_HASH = '88a1f42b01b7e2b4bf29bc1b3819b78f1e7a17cefaefbc003654f2f5cc202c2f'
NEW_HASH = '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def parse(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        assert key not in table
        assert d in ('L', 'R') and int(b) in (0, 1) and int(w) in (0, 1)
        table[key] = int(w), (-1 if d == 'L' else 1), int(z)
    return table


def state_map(q):
    return 72 if q == 90 else q


def invariant(q, h, tape):
    if q in (55, 142, 90):
        return tape[h - 1] == 1
    if q == 72:
        return tape[h - 2] == 1 and tape[h - 1] == 0
    return True


def step(table, q, h, tape):
    assert h in tape, ('read outside footprint', q, h)
    w, d, z = table[q, tape[h]]
    tape = tape.copy()
    tape[h] = w
    return z, h + d, tape


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    args.base = args.root / 'reference' / 'rotated241_old.tm'
    args.candidate = args.root / 'machines' / 'zfc240_old.tm'
    canonical_path = args.root / 'machines' / 'zfc240.tm'
    mapping_path = args.root / 'machines' / 'renumbering.json'
    if args.output is None:
        args.output = args.root / 'evidence' / 'local_independent.json'
    assert digest(args.base) == OLD_HASH
    assert digest(args.candidate) == NEW_HASH
    old, new = parse(args.base), parse(args.candidate)
    old_states = {q for q, _ in old}
    new_states = {q for q, _ in new}
    assert len(old_states) == 241 and len(old) == 482
    assert new_states == old_states - {90} and len(new) == 480
    assert set(old) - set(new) == {(90, 0), (90, 1)}
    assert {key: row for key, row in new.items() if old[key] != row} == {
        (72, 0): (0, -1, 144),
        (72, 1): (1, -1, 36),
        (79, 1): (1, 1, 72),
    }
    for table, states in ((old, old_states), (new, new_states)):
        assert {(q, b) for q in states for b in (0, 1)} == set(table)
        assert {z for w, d, z in table.values()} - states == {254}
    assert state_map(95) == 95 and state_map(254) == 254

    incoming = {q: sorted((s, b, w, d) for (s, b), (w, d, z) in old.items()
                          if z == q) for q in (55, 142, 72, 90)}
    assert incoming == {
        55: [(37, 1, 1, 1)],
        142: [(119, 1, 1, 1)],
        72: [(55, 0, 0, 1), (142, 0, 0, 1)],
        90: [(79, 1, 1, 1)],
    }
    hist = collections.Counter()
    row_durations = collections.defaultdict(set)
    paths = collections.defaultdict(set)
    count = 0
    for q in sorted(old_states):
        for bits in itertools.product((0, 1), repeat=5):
            tape = dict(zip(range(-2, 3), bits))
            if not invariant(q, 0, tape):
                continue
            z, h, target_tape = step(old, q, 0, tape)
            assert invariant(z, h, target_tape), ('invariant not preserved', q, bits)
            nq, nh, nt = state_map(q), 0, tape.copy()
            path = [(nq, nh)]
            for length in range(1, 10):
                assert nq != 254, ('premature halt', q, bits, length)
                nq, nh, nt = step(new, nq, nh, nt)
                path.append((nq, nh))
                if (nq, nh, nt) == (state_map(z), h, target_tape):
                    break
            else:
                raise AssertionError(('no positive join', q, bits, path))
            assert length in (1, 3, 9)
            hist[length] += 1
            row_durations[q, tape[0]].add(length)
            if q in (72, 90):
                paths[q, tape[0]].add(tuple(path))
            count += 1
    assert count == 7640
    assert hist == {1: 7616, 3: 20, 9: 4}
    exceptional = {key: sorted(value) for key, value in row_durations.items()
                   if value != {1}}
    assert exceptional == {(72, 0): [9], (72, 1): [3],
                           (90, 0): [3], (90, 1): [3]}
    assert all(len(ps) == 1 for ps in paths.values())
    for bits in itertools.product((0, 1), repeat=5):
        assert invariant(95, 0, dict(zip(range(-2, 3), bits)))

    order = [95] + sorted(new_states - {95})
    renaming = {q: i for i, q in enumerate(order)} | {254: 240}
    canonical = {(renaming[q], b): (w, d, renaming[z])
                 for (q, b), (w, d, z) in new.items()}
    serialized = ''.join(f'{q} {b} {w} ' + ('R' if d == 1 else 'L') + f' {z}\n'
                         for (q, b), (w, d, z) in sorted(canonical.items()))
    assert canonical_path.read_text() == serialized
    recorded_mapping = json.loads(mapping_path.read_text())
    assert recorded_mapping == {
        'old_to_new': {str(q): z for q, z in renaming.items()},
        'start': 0, 'dispatcher': renaming[96], 'halt': 240,
    }
    result = {
        'status': 'PASS_FINITE_LOCAL_ALL_TAPE_241_ROTATED_TO_240',
        'old_sha256': OLD_HASH,
        'new_sha256': NEW_HASH,
        'canonical_sha256': hashlib.sha256(serialized.encode()).hexdigest(),
        'checker_sha256': digest(Path(__file__)),
        'working_states': 240,
        'transition_rows': 480,
        'canonical_start': 0,
        'canonical_dispatcher': renaming[96],
        'canonical_halt': 240,
        'map': {'90': 72},
        'invariant': {'55': {'-1': 1}, '142': {'-1': 1},
                      '72': {'-2': 1, '-1': 0}, '90': {'-1': 1}},
        'incoming': {str(q): rows for q, rows in incoming.items()},
        'invariant_implications': count,
        'positive_whole_tape_blocks': count,
        'duration_histogram': dict(sorted(hist.items())),
        'exceptional_row_durations': {f'{q}/{b}': ds
                                      for (q, b), ds in exceptional.items()},
        'paths': {f'{q}/{b}': list(next(iter(ps))) for (q, b), ps in paths.items()},
        'read_write_and_guard_footprint': [-2, 2],
        'uninspected_exterior_unchanged': True,
        'clock_formula': 't_new = t_old + 8 V_old(72,0) + 2 V_old(72,1)'
                         ' + 2 V_old(90,0) + 2 V_old(90,1)',
        'global_conclusion': 'Two-way halting equivalence from state95 on every '
                             'binary tape and every integer head. Positive '
                             'block lengths are 1, 3, 9. The invariant holds '
                             'initially, each old step preserves it, complete '
                             'tape/head endpoints coincide, and no block '
                             'passes through halt before its endpoint.',
        'source_calibration': 'The source142 rotation is a separate proof '
                              'obligation. This checker proves the local fold '
                              'from its exact pinned 241-state table.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
