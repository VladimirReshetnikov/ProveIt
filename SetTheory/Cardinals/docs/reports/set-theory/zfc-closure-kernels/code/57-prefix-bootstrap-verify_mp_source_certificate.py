#!/usr/bin/env python3
"""Independently replay the MP0 segment relation, without its generator.

Finite source-program bisimulation only. This does not prove the binary box
contracts, source calculus calibration, or formal proof-assistant endpoint.
"""
from collections import Counter
from pathlib import Path
import argparse, hashlib, json

HERE = Path(__file__).resolve().parent

def leaf(rows, pointer):
    node = 0
    consumed = []
    for i in range(len(rows) + 1):
        bit = bool(pointer[i]) if i < len(pointer) else False
        consumed.append(bit)
        kind, argument = rows[node][int(bit)]
        if kind != 'node':
            return (kind, argument), consumed
        assert 0 <= argument < len(rows)
        node = argument
    raise AssertionError('Nonterminating source-tree descent')

def increment(pointer):
    # Retain the finite word length, including the all-zero overflow word.
    answer = list(pointer)
    for i in range(len(answer) - 1, -1, -1):
        if not answer[i]:
            answer[i] = True
            break
        answer[i] = False
    return answer

def strip(pointer, bit, number):
    answer = list(pointer)
    while number and answer:
        number -= (answer.pop() == bit)
    return answer

def segment(rows, pointer):
    increments = Counter()
    for _ in range(1000):
        (kind, argument), used = leaf(rows, pointer)
        if kind in ('decnz', 'halt'):
            return increments, list(pointer)
        if kind == 'inc':
            increments[argument] += 1
            pointer = increment(used)
        elif kind == 'brk':
            pointer = increment(strip(used, False, argument))
        elif kind == 'cont':
            pointer = strip(used, True, argument)
        else:
            raise AssertionError(('Unexpected source instruction', kind))
    raise AssertionError('Segment fuel exhausted')

def verify(directory):
    filenames = ['modified-Prog254-rows.json', 'modified-Dag254-rows.json',
                 'modified-segment-certificate.json']
    raw = [(directory / name).read_bytes() for name in filenames]
    p, d, relation = [json.loads(b) for b in raw]
    assert len(p) == 6459 and len(d) == 219 and len(relation) == 2998
    assert p[6423][1] == ['node', 6453] and d[130][1] == ['node', 167]
    assert len({(tuple(a), tuple(b)) for a, b, _, _ in relation}) == len(relation)
    ia, a = segment(p, [])
    ib, b = segment(d, [])
    assert ia == ib and relation[0][:2] == [a, b]
    edges = halts = 0
    for a, b, positive, zero in relation:
        ea, qa = leaf(p, a)
        eb, qb = leaf(d, b)
        assert ea == eb
        if ea[0] == 'halt':
            assert positive == zero == 0
            halts += 1
            continue
        assert ea[0] == 'decnz'
        for target, is_zero in [(positive, False), (zero, True)]:
            assert isinstance(target, int) and 0 <= target < len(relation)
            na = increment(strip(qa, False, 1)) if is_zero else increment(qa)
            nb = increment(strip(qb, False, 1)) if is_zero else increment(qb)
            ia, out_a = segment(p, na)
            ib, out_b = segment(d, nb)
            assert ia == ib
            assert relation[target][:2] == [out_a, out_b]
            edges += 1
    assert halts == 1 and edges == 5994
    return dict(status='passed', pairs=len(relation), checked_successor_edges=edges,
                halting_pairs=halts, initial_pair_checked=True,
                input_sha256={n: hashlib.sha256(b).hexdigest() for n, b in zip(filenames, raw)},
                scope=__doc__, new_Lean_or_Coq_build=False)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=HERE / 'mp_source_mapping')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.directory)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
