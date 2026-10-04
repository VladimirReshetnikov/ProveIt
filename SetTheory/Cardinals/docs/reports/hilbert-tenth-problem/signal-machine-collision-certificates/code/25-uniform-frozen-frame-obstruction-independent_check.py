#!/usr/bin/env python3
"""Independent finite check from literal rows; imports no upstream code."""
import json
from pathlib import Path

ROWS = {
    'A': [
        ('AR', {0, 1}, {0, 2}, (-4, 6)),
        ('AL', {0, 4}, {0, 3}, (-4, 8)),
        ('AC', {0, 1, 6}, {-1, 2, 7}, (-5, 8)),
    ],
    'B': [
        ('BR', {0, 2}, {1, 2}, (-4, 6)),
        ('BL', {0, 3}, {-1, 3}, (-5, 7)),
        ('BC', {-5, 0, 3}, {-5, 0, 1}, (-5, 8)),
    ],
}

def shift(c, a):
    return frozenset(p+a for p in c)

def raw_keys(c, block):
    found = {}
    for name, e0, e1, (lo, hi) in ROWS[block]:
        # Every present endpoint contains its minimum, an occupied site.
        # These candidate anchors are exhaustive on any finite support.
        anchors = {p-min(e) for p in c for e in (e0, e1)}
        for x in anchors:
            seen = frozenset(p-x for p in c if x+lo <= p <= x+hi)
            if seen == e0:
                found[(name, x)] = (shift(e0, x), shift(e1, x))
            elif seen == e1:
                found[(name, x)] = (shift(e1, x), shift(e0, x))
    return found

def block(c, name):
    keys = raw_keys(c, name)
    selected = []
    for key, (old, new) in keys.items():
        x = key[1]
        if any(other != key and abs(other[1]-x) <= 30 for other in keys):
            continue
        tentative = frozenset((c-old) | new)
        # The hypothetical swap cannot change keys farther than 15 away.
        # Equality of the global finite sets is the same prospective test.
        if set(raw_keys(tentative, name)) == set(keys):
            selected.append((key, old, new))
    removed, inserted = set(), set()
    for key, old, new in selected:
        assert not (removed & old)
        assert not (inserted & new)
        removed.update(old)
        inserted.update(new)
    out = frozenset((c-removed) | inserted)
    assert len(out) == len(c)
    return out

def g(c):
    return block(block(c, 'A'), 'B')

def g_inverse(c):
    return block(block(c, 'B'), 'A')

def f(c):
    return shift(g(c), 1)

def quadratic(k):
    return k*k+3*k

def main():
    cycles = 100
    end = quadratic(cycles)
    gc = frozenset((0, 5, 6, 13))
    fc = gc
    observed = []
    right_states = left_states = 0
    k = 0
    for t in range(end+1):
        while quadratic(k+1) <= t:
            k += 1
        d = 13+k
        s = t-quadratic(k)
        assert 0 <= s < 2*d-22
        if s <= d-11:
            expected = frozenset((0, 5+s, 6+s, d))
            right_states += 1
        else:
            expected = frozenset((0, 2*d-18-s, 2*d-14-s, d+1))
            left_states += 1
        assert gc == expected, (t, gc, expected)
        assert min(gc) == 0
        assert fc == shift(gc, t), (t, fc, gc)
        y = sorted(fc)
        assert y[0] == t
        sliced = (y[1]-y[0], y[2]-y[0]) == (5, 6)
        assert sliced == (s == 0), (t, y, s)
        if sliced:
            assert y == [quadratic(k), quadratic(k)+5,
                         quadratic(k)+6, quadratic(k)+13+k]
            observed.append(t)
        if t != end:
            ng, nf = g(gc), f(fc)
            assert g_inverse(ng) == gc
            assert g_inverse(shift(nf, -1)) == fc
            gc, fc = ng, nf
    assert observed == [quadratic(j) for j in range(cycles+1)]
    result = {
        'status': 'PASS',
        'method': 'New literal guarded-rule implementation; no upstream execution',
        'complete_cycles': cycles,
        'last_inclusive_time': end,
        'complete_states_checked': end+1,
        'right_phase_states_including_final_section': right_states,
        'left_phase_states': left_states,
        'slice_hits': len(observed),
        'first_10_hit_times': observed[:10],
        'last_5_hit_times': observed[-5:],
        'assertions': [
            'complete G orbit agrees with both phase formulas',
            'G minimum stays zero',
            'independently iterated F equals translation of G by t',
            'F minimum equals t',
            'slice holds exactly at s=0 and yields the exact claimed output',
            'finite-support number conservation in every executed block',
            'G inverse and F inverse undo every checked step',
        ],
        'limitation': 'Finite evidence only; proof.md gives the all-time deduction from Report 49',
    }
    output = Path(__file__).with_name('check_result.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
