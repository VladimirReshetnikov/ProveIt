"""Audit the uniform residual-twist degree consequence in arXiv:2606.22410v1.

An explicit trefoil crossing is replaced by an odd anti-parallel twist.
Independent cube Jones values, a skein recurrence, quadratic recovery, and
formal JVP substitution are cross-checked. Local smoothing/RII traces retain
the fixed exterior. No claimed clasp-machine isotopy is assumed or replayed.
"""
import argparse
from collections import defaultdict
from itertools import product
import json
from math import comb
from pathlib import Path
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
from fastunknot import Diagram
from fastunknot.faithful_jones import faithful_potts_exact
from check_potts_independent import laurent_jones

HOST = ((5, 1, 2, 0), (1, 4, 3, 2), (0, 3, 4, 5))


def twist_pd(length, signs=None):
    if type(length) is not int or length < 1 or length % 2 != 1:
        raise ValueError('length must be positive and odd')
    signs = [1]*length if signs is None else list(signs)
    if len(signs) != length or any(s not in (-1, 1) for s in signs):
        raise ValueError('one crossing sign per residual crossing is required')
    rows = list(HOST[:2])
    a, b = HOST[2][:2]
    for i, sign in enumerate(signs):
        c, d = HOST[2][2:] if i == length-1 else (6+2*i, 7+2*i)
        row = (a, b, c, d)
        rows.append(row if sign == 1 else row[1:]+row[:1])
        a, b = d, c
    return rows


def canonical(rows):
    labels = {}
    return [[labels.setdefault(x, len(labels)) for x in row] for row in rows]


class Joins:
    def __init__(self, pd):
        self.parent = {x: x for row in pd for x in row}

    def root(self, x):
        while self.parent[x] != x:
            x = self.parent[x]
        return x

    def join(self, x, y):
        self.parent[self.root(x)] = self.root(y)

    def rows(self, rows):
        return [[self.root(x) for x in row] for row in rows]


def incoming(pd):
    """Independent traversal of opposite ports and equal-label arc ends."""
    ends = defaultdict(list)
    for i, row in enumerate(pd):
        for slot, label in enumerate(row):
            ends[label].append((i, slot))
    assert all(len(darts) == 2 for darts in ends.values())
    result, seen, dart = defaultdict(set), set(), (0, 0)
    while dart not in seen:
        seen.add(dart)
        i, slot = dart
        result[i].add(slot)
        opposite = (i, (slot+2) % 4)
        pair = ends[pd[i][opposite[1]]]
        dart = pair[0] if pair[1] == opposite else pair[1]
    assert dart == (0, 0) and len(seen) == 2*len(pd)
    assert all(len(slots) == 2 for slots in result.values())
    return result


def smoothing_traces(length):
    """Every oriented smoothing deletes the other twist rows by local RI.

All surviving exterior port connections equal those of the smoothed host.
The monogon criterion is independent of the over/under signs of live rows.
"""
    pd = twist_pd(length)
    direction = incoming(pd)
    host = Joins(HOST)
    host.join(0, 3)
    host.join(4, 5)
    expected = canonical(host.rows(HOST[:2]))
    traces = []
    for seed in range(2, length+2):
        assert len(direction[seed] & {0, 1}) == 1  # anti-parallel in the twist band
        assert len(direction[seed] & {2, 3}) == 1
        joins = Joins(pd)
        a, b, c, d = pd[seed]
        joins.join(a, b)
        joins.join(c, d)
        live, moves = set(range(2, length+2))-{seed}, []
        while live:
            found = False
            for i in sorted(live):
                row = [joins.root(x) for x in pd[i]]
                for slot in range(4):
                    if row[slot] == row[(slot+1) % 4]:
                        joins.join(row[(slot+2) % 4], row[(slot+3) % 4])
                        moves.append([i, slot])
                        live.remove(i)
                        found = True
                        break
                if found:
                    break
            assert found, (length, seed, live)
        remaining = canonical(joins.rows(pd[:2]))
        assert remaining == expected
        traces.append(dict(smoothed_row=seed, ri_moves=moves, exterior_rows=remaining))
    return traces


def anchor_trace(length):
    """Cancel fixed adjacent opposite-sign pairs inside the planted disk."""
    base = twist_pd(length)
    signs = [1, -1]*((length-1)//2)+[1]
    signed = twist_pd(length, signs)
    joins, moves = Joins(base), []
    for i in range(2, length+1, 2):
        left, right = base[i:i+2]
        assert left[3] == right[0] and left[2] == right[1]
        assert signs[i-2] == -signs[i-1]
        joins.join(left[0], right[3])
        joins.join(left[1], right[2])
        moves.append([i, i+1])
    remaining = canonical(joins.rows(signed[:2]+signed[-1:]))
    assert remaining == canonical(HOST)
    return dict(signs=signs, rii_pairs=moves, reduced_rows=remaining)


def recurrence(length):
    """Positive twist family: V_L=t^2 V_(L-2)+t-t^2+t^3-t^4."""
    polynomial = {1: 1, 3: 1, 4: -1}
    for _ in range(3, length+1, 2):
        p = defaultdict(int, {k+2: v for k, v in polynomial.items()})
        for k, v in ((1, 1), (2, -1), (3, 1), (4, -1)):
            p[k] += v
        polynomial = {k: v for k, v in p.items() if v}
    return polynomial


def smoothed_host_polynomial():
    """Four-state bracket check in x=t^(1/2) for the oriented Hopf smoothing."""
    joins = Joins(HOST)
    joins.join(0, 3)
    joins.join(4, 5)
    pd = joins.rows(HOST[:2])
    answer = defaultdict(int)
    for bits in range(4):
        state = Joins(pd)
        for i, (a, b, c, d) in enumerate(pd):
            pairs = ((a, d), (b, c)) if bits & (1 << i) else ((a, b), (c, d))
            for left, right in pairs:
                state.join(left, right)
        circles = len({state.root(x) for row in pd for x in row})
        # Both surviving host crossings are positive: n=2, writhe=2.
        exponent_a = 2-2*bits.bit_count()-3*2+2*(circles-1)
        assert exponent_a % 2 == 0
        for j in range(circles):
            answer[-exponent_a//2+2*j] += (-1)**(2+circles-1)*comb(circles-1, j)
    answer = {k: v for k, v in answer.items() if v}
    assert answer == {1: -1, 5: -1}
    return answer


def jvp(polynomial):
    """Reduce V(t), t=x^2, into a(p)+b(p)x with x^2=px+1.

This formal polynomial recurrence is separate from the production numeric
quadratic ring x^2-Mx+1. A substitution check recovers the input Laurent form.
"""
    answer = [defaultdict(int), defaultdict(int)]
    for degree, coefficient in polynomial.items():
        pair = ({0: 1}, {})
        for _ in range(abs(2*degree)):
            a, b = pair
            if degree >= 0:
                second = defaultdict(int, a)
                for j, value in b.items():
                    second[j+1] += value
                pair = (dict(b), dict(second))
            else:
                first = defaultdict(int, b)
                for j, value in a.items():
                    first[j+1] -= value
                pair = (dict(first), dict(a))
        for component in (0, 1):
            for j, value in pair[component].items():
                answer[component][j] += coefficient*value
    answer = [{j: v for j, v in sorted(p.items()) if v} for p in answer]
    reconstructed = defaultdict(int)
    for offset, p in enumerate(answer):
        for j, value in p.items():
            for k in range(j+1):
                reconstructed[j-2*k+offset] += value*(-1)**k*comb(j, k)
    assert {j: v for j, v in reconstructed.items() if v} == {2*j: v for j, v in polynomial.items()}
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    hopf = smoothed_host_polynomial()
    rows, cube_comparisons, signed_checks = [], 0, 0
    for length in (1, 3, 5, 7, 9, 23, 31):
        pd = twist_pd(length)
        smoothings, anchor = smoothing_traces(length), anchor_trace(length)
        diagram = Diagram.from_pd(pd)
        assert diagram.writhe() == length+2
        for mirrored in (False, True):
            d = diagram.mirror() if mirrored else diagram
            expected = recurrence(length)
            if mirrored:
                expected = {-k: v for k, v in expected.items()}
            if length <= 9:
                cube = {-k: v for k, v in laurent_jones(d).items()}
                assert cube == expected
                cube_comparisons += 1
            full = faithful_potts_exact(d, include_polynomial=True,
                                       max_states=None, max_transitions=None)
            polynomial = {k: int(v, 16) for k, v in full['jones_polynomial']['coefficients_hex']}
            assert polynomial == expected
            a, b = jvp(polynomial)
            degree = max(set(a) | set(b))
            assert degree == 2*length+(6 if mirrored else 5)
            rows.append(dict(length=length, mirrored=mirrored, pd=d.pd,
                             host_crossings=3, host_components=1, implied_residual_cap=22,
                             polynomial=sorted(polynomial.items()), jvp_a=sorted(a.items()),
                             jvp_b=sorted(b.items()), jvp_degree=degree,
                             violates_cap=degree > 22, cube_checked=length <= 9,
                             smoothing_traces=smoothings if not mirrored else None,
                             anchor_trace=anchor if not mirrored else None))
    # Exhaust small sign cubes: verify the geometric RII reduction's invariant.
    # A word of +/- twists cancels to its signed sum, including negative sums.
    for length in (1, 3, 5):
        for signs in product((-1, 1), repeat=length):
            d = Diagram.from_pd(twist_pd(length, signs))
            exponent = sum(signs)
            target = Diagram.from_pd(twist_pd(abs(exponent), [1 if exponent > 0 else -1]*abs(exponent)))
            assert laurent_jones(d) == laurent_jones(target)
            signed_checks += 1
    result = dict(status='PASS', source='https://arxiv.org/html/2606.22410v1',
                  scope='Contradiction to the joint uniform residual-cap and universal realization claims; '
                        'not a counterexample to Jones unknot detection and not a localization of the machine error',
                  host_pd=HOST, smoothed_host_x_polynomial=sorted(hopf.items()),
                  independent_cube_comparisons=cube_comparisons,
                  signed_state_checks=signed_checks, rows=rows)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))
    print('length / mirrored / JVP degree / claimed cap')
    for row in rows:
        print(row['length'], row['mirrored'], row['jvp_degree'], row['implied_residual_cap'])


if __name__ == '__main__':
    main()
