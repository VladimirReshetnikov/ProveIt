#!/usr/bin/env python3
"""Separate sparse interpreter and complete register-block decoding.

This module intentionally does not import the primary parser or tape interpreter.
Both literal blank runs are compared over the complete finite support. All
nonlisted cells are zero by the representation, including both infinite ends.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json


def require(value, message):
    if not value:
        raise ValueError(message)


def parse(path):
    table, starts = {}, []
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q, r, w, d, z = line.split()
            key = int(q), int(r)
            require(key not in table, 'Duplicate row')
            require(r in ('0', '1') and w in ('0', '1') and d in ('L', 'R'), 'Malformed row')
            table[key] = int(w), 1 if d == 'R' else -1, int(z)
    states = {q for q, bit in table}
    require(starts == [0] and set(table) == {(q,b) for q in states for b in (0,1)}, 'Malformed table')
    require({z for w,d,z in table.values()} - states == {230}, 'Unexpected halt')
    return table


def run(table, count):
    state = head = 0
    ones = set()
    visits = Counter()
    lo = hi = 0
    for _ in range(count):
        row = state, int(head in ones)
        visits[row] += 1
        write, move, state = table[row]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        lo, hi = min(lo, head), max(hi, head)
    return dict(steps=count, state=state, head=head, one_cells=sorted(ones),
                visited_rows=[dict(row=list(k),count=v) for k,v in sorted(visits.items())],
                minimum_head=lo, maximum_head=hi)


def main():
    package = Path(__file__).resolve().parent.parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, default=package/'inputs/k230.tm')
    ap.add_argument('--candidate', type=Path, default=package/'machines/k228_original_labels.tm')
    ap.add_argument('--output', type=Path, default=package/'rerun/startup_independent.json')
    args = ap.parse_args()
    old, new = parse(args.baseline), parse(args.candidate)
    before, after = run(old,408419), run(new,409835)
    require((before['state'],before['head'],before['one_cells']) ==
            (after['state'],after['head'],after['one_cells']), 'Complete seed configurations disagree')
    require((after['state'],after['head'],len(after['one_cells'])) == (84,-5,351), 'Wrong endpoint')
    support = set(after['one_cells'])
    require(min(support) == after['head']-1, 'Wrong marker or nonblank left exterior')
    header = min(p for p in support if p >= after['head'])
    pos, last, values = header+1, max(support), []
    while pos <= last:
        require(pos not in support and pos+1 in support, 'Malformed register block')
        pos += 1
        start = pos
        while pos in support:
            pos += 1
        values.append(pos-start-1)
    require(pos == last+1 and header == 176, 'Wrong register frame')
    require(values[:9] == [0,0,0,3,0,0,3,0,0] and values[9:] == [1]*167,
            'Wrong primary or spare values')
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    receipt = dict(status='PASS_INDEPENDENT_SPARSE_STARTUP_AND_COMPLETE_SEED_DECODING',
        original=before,candidate=after,header=header,marker=after['head']-1,
        physical_primary_values=values[:9],spare_count=167,spare_value=1,
        original_sha256=digest(args.baseline),candidate_sha256=digest(args.candidate),
        checker_sha256=digest(Path(__file__)),
        support_sha256=hashlib.sha256((json.dumps(after['one_cells'],separators=(',',':'))+'\n').encode()).hexdigest(),
        complete_tapes_equal=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: independent full-support comparison and decoding; K230 408419, K228 409835 steps')


if __name__ == '__main__':
    main()
