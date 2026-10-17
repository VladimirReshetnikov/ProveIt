#!/usr/bin/env python3
"""Produce and independently check a finite exact-quotient obstruction.

For every pair of working states, a read word distinguishes their labeled
transition trees. These are free words over {0,1}, not assertions that every
such word is a physical TM tape trace. They suffice to prohibit a homomorphism
of the full transition structure that identifies those states.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_TABLE = HERE / 'vendor/busy-beaver/ZF/m253/machine/zfc_253.tm'
PIN = '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'


def parse_table(path):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == PIN
    rows = {}
    for line in data.decode('ascii').splitlines():
        if line.startswith('#'):
            continue
        q, read, write, move, target = line.split()
        key = int(q), int(read)
        assert key not in rows
        rows[key] = int(write), move, int(target)
    assert set(rows) == {(q, b) for q in range(253) for b in (0, 1)}
    assert all(w in (0, 1) and d in ('L', 'R') and 0 <= n <= 253 for w, d, n in rows.values())
    return rows


def construct(rows):
    reverse = defaultdict(list)
    witnesses = {}
    todo = deque()
    for p, q in itertools.combinations(range(254), 2):
        pair = p, q
        if q == 253:
            witnesses[pair] = ''
            todo.append(pair)
            continue
        for b in (0, 1):
            left, right = rows[p, b], rows[q, b]
            if left[:2] != right[:2]:
                if pair not in witnesses:
                    witnesses[pair] = str(b)
                    todo.append(pair)
            elif left[2] != right[2]:
                successor = tuple(sorted((left[2], right[2])))
                reverse[successor].append((pair, str(b)))
    while todo:
        target = todo.popleft()
        for pair, symbol in reverse[target]:
            if pair not in witnesses:
                witnesses[pair] = symbol + witnesses[target]
                todo.append(pair)
    assert len(witnesses) == 254 * 253 // 2
    return [[p, q, witnesses[p, q]] for p, q in itertools.combinations(range(253), 2)]


def check_word(rows, p, q, word):
    # This checker does not use refinement classes, BFS, or certificate parent links.
    for bit in word:
        assert bit in '01'
        if (p == 253) != (q == 253):
            return True
        if p == 253:
            return False
        left = rows[p, int(bit)]
        right = rows[q, int(bit)]
        if left[:2] != right[:2]:
            return True
        p, q = left[2], right[2]
    return (p == 253) != (q == 253)


def verify(rows, certificate):
    assert certificate['table_sha256'] == PIN
    checked = set()
    lengths = Counter()
    for p, q, word in certificate['witnesses']:
        assert 0 <= p < q < 253 and (p, q) not in checked
        assert check_word(rows, p, q, word), (p, q, word)
        checked.add((p, q))
        lengths[len(word)] += 1
    assert checked == set(itertools.combinations(range(253), 2))
    return {'working_state_pairs_checked': len(checked),
            'maximum_distinguishing_word_length': max(lengths),
            'word_length_histogram': dict(sorted(lengths.items())),
            'injectivity_of_exact_transition_quotient': True,
            'lower_bound_on_other_equivalent_TMs': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, default=DEFAULT_TABLE)
    parser.add_argument('--certificate', type=Path, default=HERE / 'no-quotient253-certificate.json')
    parser.add_argument('--check', action='store_true', help='check the existing artifact without recomputing witnesses')
    args = parser.parse_args()
    rows = parse_table(args.table)
    if args.check:
        result = json.loads(args.certificate.read_text())
    else:
        result = {'table_sha256': PIN, 'source_commit': '0d544f2a2e3c18f12278441a74b7879f31cbe856',
                  'witness_semantics': 'free input words distinguish full transition trees',
                  'witnesses': construct(rows)}
        args.certificate.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    report = verify(rows, result)
    if not args.check:
        (HERE / 'no-quotient253-results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
