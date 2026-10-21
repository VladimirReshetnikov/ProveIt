#!/usr/bin/env python3
"""Reproduce a wrong full-tape return after the rejected reset-state deletion."""
import argparse, hashlib, json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE_SHA = 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)

def table(raw):
    result = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, w, d, z = line.split()
        result[int(q), int(bit)] = int(w), (-1 if d == 'L' else 1), int(z)
    return result

def frame(pc, registers, spares):
    ones = {-1, 64}
    ones.update(i for i, x in enumerate(pc) if x == '1')
    physical = [0] * 9
    for i, value in enumerate(registers):
        physical[PHY[i]] = value
    pos = 65
    for value in physical + spares:
        pos += 1
        ones.update(range(pos, pos + value + 1))
        pos += value + 1
    return ones

def clean_dispatch(q, head, ones):
    # Same explicit frame predicate as the pinned independent runtime,
    # expressed in native state names (84 is legacy dispatcher 96).
    if q != 84 or head - 1 not in ones or any(x < head - 1 for x in ones):
        return False
    right = sorted(x for x in ones if x >= head + 52)
    if not right or right[0] < head + 64:
        return False
    pos, last, count = right[0] + 1, max(ones), 0
    while pos < last:
        if pos in ones or pos + 1 not in ones:
            return False
        pos += 1
        while pos in ones:
            pos += 1
        count += 1
    return pos == last + 1 and count >= 10

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline219', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    assert __debug__, 'Assertions must be enabled'
    raw = (args.baseline219 / 'machine/k219.native.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == BASE_SHA
    original = table(raw)
    modified = dict(original)
    modified[34, 0] = (0, -1, 75)
    modified = {k: v for k, v in modified.items() if k[0] != 50}
    assert modified == table((HERE / 'drop50.tm').read_bytes())
    assert len(modified) == 436
    saved = json.loads((HERE / 'drop50_counterexample.json').read_text())
    expected = frame(saved['expected_logical']['pc'], [0] * 9, [0])
    assert expected == set(saved['expected']['ones'])
    initial = frame(saved['site'][0], [0] * 9, [0])
    answers = {}
    for name, machine in [('baseline219', original), ('rejected218', modified)]:
        ones = set(initial)
        q, head = 84, 0
        for tick in range(1, 20001):
            w, direction, q = machine[q, int(head in ones)]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += direction
            if clean_dispatch(q, head, ones):
                break
        else:
            raise AssertionError('No return in the stated diagnostic bound')
        answers[name] = dict(steps=tick, native_state=q, head=head,
                             ones=sorted(ones), exact_expected_tape=(ones == expected))
    assert answers['baseline219']['exact_expected_tape']
    bad = answers['rejected218']
    assert bad['steps'] == 662 and not bad['exact_expected_tape']
    assert bad['ones'] == saved['actual']['ones']
    result = dict(status='EXPECTED_COUNTEREXAMPLE_REPRODUCED', results=answers,
                  scope='A supplied valid primitive frame; no blank-run reachability claim.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])

if __name__ == '__main__':
    main()
