#!/usr/bin/env python3
"""Replay the bounded QNS5 three-way control-sharing screen.

Python 3, standard library only. Frozen local inputs; no compiler imports,
network access, repository checkout, or search_compose dependency.
This is a restricted negative experiment, not a state-count lower bound.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import time

HERE = Path(__file__).resolve().parent
ALIAS = {41: 99, 330: 99}
LEFT_WIDTH, WIDTH, ITERATIONS = 8, 11, 50


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        assert bit in (0, 1) and write in (0, 1)
        assert direction in ('L', 'R') and (q, bit) not in rows
        rows[q, bit] = write, direction == 'R', target
    controls = {q for q, bit in rows}
    assert len(rows) == 2 * len(controls)
    return rows


def apply_folds(rows, folds):
    """The disjoint seven AX folds, with simultaneous target redirection."""
    aliases = {a: b for a, b, actions in folds}
    actions = {b: acts for a, b, acts in folds}
    assert len(aliases) == len(folds)
    assert len({q for a, b, acts in folds for q in (a, b)}) == 2 * len(folds)
    out = {}
    for (q, bit), act in rows.items():
        if q in aliases:
            continue
        w, d, target = actions[q][bit] if q in actions else act
        out[q, bit] = w, bool(d), aliases.get(target, target)
    return out


def verify_manifest():
    manifest = json.loads((HERE / 'MANIFEST.json').read_text())
    for name, expected in manifest.items():
        actual = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        assert actual == expected, ('file hash mismatch', name, expected, actual)


def prepare():
    raw = read_table(HERE / 'data/raw.native.tm')
    folds = json.loads((HERE / 'data/AXfolds.json').read_text())
    assert len(raw) == 406 and len(folds) == 7
    folded = apply_folds(raw, folds)
    assert len(folded) == 392
    rows = {(q, bit): (w, d, ALIAS.get(target, target))
            for (q, bit), (w, d, target) in folded.items() if q not in ALIAS}
    assert len(rows) == 388
    # These names belong to this QNS5 construction. In QN5, 330 instead
    # names the multiplier helper; that is a different table.
    assert raw[330, 0] == (0, True, 63)
    assert raw[330, 1] == (1, False, 73)
    assert raw[331, 0] == (0, True, 61)
    assert raw[331, 1] == (1, True, 99)
    contexts = json.loads((HERE / 'data/contexts.json').read_text())
    assert {q: len(v) for q, v in contexts.items()} == {
        '41': 163, '99': 150, '330': 4, '331': 56}
    cases = {0: [], 1: []}
    for q in (41, 99, 330):
        for left, right in contexts[str(q)]:
            assert set(left + right) <= {'0', '1'}
            assert len(left) <= LEFT_WIDTH and 1 <= len(right) <= WIDTH - LEFT_WIDTH
            left = left.rjust(LEFT_WIDTH, '0')
            right = right.ljust(WIDTH - LEFT_WIDTH, '0')
            bit = int(right[0])
            tape = tuple(map(int, left + right))
            w, d, target = raw[q, bit]
            endpoint = list(tape)
            endpoint[LEFT_WIDTH] = w
            target = ALIAS.get(target, target)
            cases[bit].append((q, tape, (target, LEFT_WIDTH + (1 if d else -1),
                                        tuple(endpoint))))
    assert {bit: len(v) for bit, v in cases.items()} == {0: 211, 1: 106}
    return rows, cases


def run(rows, case, action0, action1):
    """Original bounded-loop semantics, including its endpoint-check boundary.

    True: exact one-step endpoint reached after 1..49 transitions.
    None: the missing row was encountered during one-row screening.
    False: window exit, missing transition, or exhaustion of 50 iterations.
    There is deliberately no endpoint check after the 50th transition.
    """
    old_q, tape, endpoint = case
    q, head, mutable = 99, LEFT_WIDTH, list(tape)
    for iteration in range(ITERATIONS):
        if iteration and (q, head, tuple(mutable)) == endpoint:
            return True
        if head < 0 or head >= WIDTH:
            return False
        bit = mutable[head]
        if q == 99:
            action = action1 if bit else action0
            if action is None:
                return None
        else:
            action = rows.get((q, bit))
        if action is None:
            return False
        write, direction, q = action
        mutable[head] = write
        head += 1 if direction else -1
    return False


def search(rows, cases):
    controls = sorted({q for q, bit in rows})
    candidates = []
    for bit in (0, 1):
        surviving = []
        for write, direction, target in itertools.product((0, 1), (False, True), controls):
            action = write, direction, target
            action0 = action if bit == 0 else None
            action1 = action if bit == 1 else None
            if all(run(rows, case, action0, action1) is not False for case in cases[bit]):
                surviving.append(action)
        candidates.append(surviving)
    hits = []
    for action0, action1 in itertools.product(*candidates):
        if all(run(rows, case, action0, action1) is True
               for bit in (0, 1) for case in cases[bit]):
            hits.append((action0, action1))
    return {'cases': {str(bit): len(v) for bit, v in cases.items()},
            'candidates': json.loads(json.dumps(candidates)),
            'hits': json.loads(json.dumps(hits))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'replay',
                        help='Directory for the regenerated receipt (default: ./replay).')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Do not run Python with -O: assertions verify input and output identities.')
    verify_manifest()
    rows, cases = prepare()
    started = time.perf_counter()
    result = search(rows, cases)
    elapsed = time.perf_counter() - started
    original = json.loads((HERE / 'recorded/original_search.json').read_text())
    assert result == {key: original[key] for key in ('cases', 'candidates', 'hits')}
    result.update({
        'raw_controls': 203, 'after_AX_folds': 196, 'attempted_controls': 194,
        'contexts_for_control_331_used': False,
        'actions_tested_per_row': 4 * 194,
        'candidate_pairs_checked': len(result['candidates'][0]) * len(result['candidates'][1]),
        'window_cells': WIDTH, 'initial_head_index': LEFT_WIDTH,
        'transition_iterations': ITERATIONS, 'accepted_endpoint_steps': [1, 49],
        'seconds': elapsed, 'kernel_checked': False,
        'status': 'No hit in this frozen-context bounded screen; no lower bound claimed.'})
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'search.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
