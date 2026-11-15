#!/usr/bin/env python3
"""Replay a rejected root reassociation on one complete finite-support tape.

No symbolic runtime or compiled arithmetic macro is called.  Source resolution
is used only to establish what instruction and continuation the test must have.
The TM trace is a literal set-of-one-cells simulation.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read_table(p):
    rows = {}
    for line in p.read_text().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in rows and b in (0, 1) and w in (0, 1)
        assert d in ('L', 'R')
        rows[q, b] = (w, 1 if d == 'R' else -1, n)
    return rows


def frame(path, logical, gap):
    physical_permutation = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    physical = [0] * 9
    for i, p in enumerate(physical_permutation):
        physical[p] = logical[i]
    # The test has one unit spare and head zero; the zero exterior is implicit.
    ones = {-1, 48 + gap}
    ones.update(i for i, bit in enumerate(path) if bit == '1')
    pos = 49 + gap
    for value in physical + [1]:
        pos += 1
        ones.update(range(pos, pos + value + 1))
        pos += value + 1
    return ones


def run(rows, source_path, target_path, L, gap):
    logical = [0] * 9
    logical[8] = L
    ones = frame(source_path, logical, gap)
    initial = sorted(ones)
    expected = frame(target_path, logical, gap)
    q, h = 84, 0
    for steps in range(1, 25001):
        w, move, q = rows[q, int(h in ones)]
        (ones.add if w else ones.discard)(h)
        h += move
        if (q, h, ones) == (84, 0, expected):
            outcome = 'expected_source_frame'
            break
        if q == 254:
            outcome = 'incorrect_early_halt'
            break
    else:
        outcome = 'unresolved_within_bound'
    return {'L': L, 'gap': gap, 'steps': steps, 'outcome': outcome,
            'initial_state': 84, 'initial_head': 0,
            'initial_ones': initial, 'expected_ones': sorted(expected),
            'final_state': q, 'final_head': h, 'final_ones': sorted(ones)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mp', type=Path, required=True,
                    help='Path to the accompanying mp_construction component')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    R = args.mp / 'reference'
    assert digest(R / 'raw.native.tm') == '60a560a90db1b698ba8b1456917dc4fd3c5156901e2b90f3ab0262c50010aa3b'
    spec = importlib.util.spec_from_file_location('source_resolver', args.mp / 'code/source.py')
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    nodes = json.loads((R / 'nodes.json').read_text())
    grammar = json.loads((R / 'grammar.json').read_text())
    old_sites, old_ins = source.resolve(nodes, grammar)
    assert old_sites == json.loads((R / 'sites.json').read_text())
    assert old_ins == json.loads((R / 'instructions.json').read_text())
    assert nodes['node172'] == ['node21', 'node171']
    assert nodes['node21'] == ['node7', 'node20']
    assert nodes['node171'] == ['node170', 'node23']
    nodes['node172'] = ['node7', [['node20', 'node170'], 'node23']]
    sites, ins = source.resolve(nodes, grammar)
    assert ins == old_ins
    assert sites[11] == ['100000', 'dec', 2]
    assert ins[11] == ['dec', 2, 19, 12]
    assert sites[19][0] == '100010'
    rows = read_table(R / 'raw.native.tm')
    edits = {(84, 0): 68, (310, 0): 53, (53, 0): 69, (53, 1): 214}
    delta = []
    for key, target in edits.items():
        old = rows[key]
        rows[key] = (*old[:2], target)
        delta.append({'state': key[0], 'read': key[1], 'old': old, 'new': rows[key]})
    cases = [run(rows, sites[11][0], sites[19][0], L, gap)
             for L in (0, 1) for gap in (0, 1)]
    assert [(x['outcome'], x['steps']) for x in cases] == [
        ('expected_source_frame', 468), ('expected_source_frame', 476),
        ('incorrect_early_halt', 17392), ('incorrect_early_halt', 17648)]
    result = {'status': 'PASS', 'claim': 'Literal refutation of the all-register primitive contract for this exact rejected root rotation',
              'scope_limit': 'This does not refute blank-input equivalence of every possible alternative root encoding or rule out other 193-state constructions.',
              'reference_raw_sha256': digest(R / 'raw.native.tm'),
              'resolved_instruction_identity': True, 'source_sites': len(sites),
              'source_site': 11, 'source_path': sites[11][0], 'source_instruction': ins[11],
              'expected_target': 19, 'expected_path': sites[19][0],
              'changed_rows': delta, 'cases': cases}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('cases', 'changed_rows')}, indent=2))


if __name__ == '__main__':
    main()
