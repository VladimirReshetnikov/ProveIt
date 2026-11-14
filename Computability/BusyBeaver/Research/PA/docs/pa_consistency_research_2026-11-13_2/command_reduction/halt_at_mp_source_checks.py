#!/usr/bin/env python3
"""Bounded, exact-integer checks of the concrete halt-at-MP source tree.

This program uses only the Python standard library.  Its default input is the
adjacent literal source snapshot.  It resolves relative jumps independently
from leaf paths, checks the MP/Shift register contracts, and writes JSON evidence.
These are regression checks, not a universal tape-refinement certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE_SHA256 = "9b3886a936eb72baa609413c3579c1808c2f3af81468d4260eae680c0dc2d468"
FETCH, MP_ENTRY, SUCCESS, SHIFT_ENTRY = 14, 3682, 3762, 3782


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (math.isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def resolve(rows):
    """Resolve by ordered subtree intervals and outward ancestor traversal."""
    leaves = {p: i for i, (p, _, _) in enumerate(rows)}
    assert len(leaves) == len(rows)
    intervals = {}

    def visit(p):
        if p in leaves:
            result = (leaves[p], leaves[p] + 1)
        else:
            a, b = visit(p + '0'), visit(p + '1')
            assert a[1] == b[0]
            result = (a[0], b[1])
        intervals[p] = result
        return result

    assert visit('') == (0, len(rows))

    def outward(p, edge, count):
        while p:
            last, p = p[-1], p[:-1]
            if last == edge:
                count -= 1
                if count == 0:
                    lo, hi = intervals[p]
                    return hi % len(rows) if edge == '0' else lo
        return 0

    result = []
    for i, (p, op, arg) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == 'CI':
            result.append(('inc', arg, after))
        elif op == 'CD':
            result.append(('dec', arg, outward(p, '0', 1), after))
        elif op == 'CB':
            result.append(('jump', outward(p, '0', arg)))
        elif op == 'CC':
            result.append(('jump', outward(p, '1', arg)))
        else:
            assert op == 'CH'
            result.append(('halt',))
    return result


def run(graph, start, registers, limit=2_000_000):
    """Stop on source halt or on return to command fetch, with the full frame."""
    r, pc = list(registers), start
    for steps in range(limit):
        if pc == FETCH:
            return 'return', r, steps
        instruction = graph[pc]
        op = instruction[0]
        if op == 'halt':
            return 'halt', r, steps
        if op == 'jump':
            pc = instruction[1]
        elif op == 'inc':
            r[instruction[1]] += 1
            pc = instruction[2]
        else:
            assert op == 'dec'
            reg = instruction[1]
            if r[reg] == 0:
                pc = instruction[2]
            else:
                r[reg] -= 1
                pc = instruction[3]
    raise AssertionError(('step bound exhausted', start, registers, r, pc))


def frame(t, w, d, h, l, marker=7):
    # N,T,W,A,D,H,X,Y,L.  N and A are irrelevant to these tested macros.
    return [marker, t, w, marker + 1, d, h, 0, 0, l]


def main():
    if not __debug__:
        raise RuntimeError('Run without Python -O or -OO; assertions are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sites', type=Path,
                        default=HERE / 'halt_at_mp_source_sites.json')
    parser.add_argument('--output', type=Path,
                        default=HERE / 'halt_at_mp_source_checks.json')
    args = parser.parse_args()
    raw = args.sites.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == SOURCE_SHA256, ('different source snapshot', digest)
    rows = json.loads(raw)
    assert len(rows) == 3788
    graph = resolve(rows)
    assert [i for i, row in enumerate(graph) if row[0] == 'halt'] == [3780]
    assert graph[3781] == ('jump', FETCH)
    assert graph[3787] == ('jump', 0)
    counts = {'success_branch': 0, 'full_mp': 0, 'total_shift': 0}
    maximum_steps = {key: 0 for key in counts}

    # Arithmetic success branch, including b=0 (the truth-code alias) and b=1.
    for b, w, l in itertools.product(range(20), range(4), range(3)):
        initial = frame(0, w, b, 0, l)
        status, got, steps = run(graph, SUCCESS, initial)
        assert status == ('halt' if b == 1 else 'return'), (b, w, l, status)
        expected = frame(b, w, 0, 0, l)
        assert got == expected, (b, w, l, got, expected)
        counts['success_branch'] += 1
        maximum_steps['success_branch'] = max(maximum_steps['success_branch'], steps)

    # Complete source MP consumes one Cantor-coded offset from L.  Test both
    # branches, including the exact comparison boundary and arbitrary frames.
    for t, d, x, w, tail in itertools.product(range(4), range(4), range(4), range(3), range(3)):
        b = d + x
        major = 4 * pair(t, b)
        for h in sorted({0, 1, major, major + 1}):
            initial = frame(t, w, d, h, pair(x, tail), marker=11)
            status, got, steps = run(graph, MP_ENTRY, initial)
            success = major == h
            assert status == ('halt' if success and b == 1 else 'return')
            expected = frame(b if success else 0, w, 0 if success else b,
                             0, tail, marker=11)
            assert got == expected, (t, d, x, w, tail, h, got, expected)
            counts['full_mp'] += 1
            maximum_steps['full_mp'] = max(maximum_steps['full_mp'], steps)

    # Total Shift clears the old T, transfers H, and decodes W at the root.
    for t, h, w, d, l in itertools.product(range(4), range(4), range(20), range(3), range(2)):
        initial = frame(t, w, d, h, l, marker=13)
        status, got, steps = run(graph, SHIFT_ENTRY, initial)
        a, rest = unpair(w)
        expected = frame(h, rest, d, a, l, marker=13)
        assert status == 'return' and got == expected, (initial, status, got, expected)
        counts['total_shift'] += 1
        maximum_steps['total_shift'] = max(maximum_steps['total_shift'], steps)

    result = {
        'source_sha256': digest,
        'source_sites': len(rows),
        'checked_contracts': counts,
        'maximum_source_steps': maximum_steps,
        'status': 'passed',
        'scope': ('Bounded checks of literal source MP/Shift including all nine '
                  'registers; no physical binary TM or universal source proof '
                  'is certified by this regression script.'),
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
