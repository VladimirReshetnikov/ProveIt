#!/usr/bin/env python3
"""Exact finite checks for the torsion-packet growth theorem.

This verifies finite instances of the proof ingredients, not the asymptotic theorem.
Only Python's standard library is used. Output is deterministic JSON.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def ep(p, h):
    return (p - 1) * p ** (h - 1)


def vp(n, p):
    assert n != 0
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def excess(a, b, p, h):
    if a == b:
        return None  # positive infinity
    return F(p ** vp(a - b, p) - 1, ep(p, h))


def capacity(p, h, m):
    e = ep(p, h)
    if m == e:
        return None
    return sum((F(ep(p, j) * (m // ep(p, j)), e)
                for j in range(1, h)), F(0))


def greedy_checks():
    count = 0
    for p, hmax in [(2, 6), (3, 4), (5, 3)]:
        for h in range(1, hmax + 1):
            units = [a for a in range(1, p ** h) if a % p]
            e = ep(p, h)
            for m in range(e):
                values = []
                for a in units[m:]:
                    values.append(sum((excess(a, b, p, h)
                                       for b in units[:m]), F(0)))
                assert min(values) == capacity(p, h, m)
                count += 1
    return count


def root_average_checks():
    count = 0
    for p, hmax in [(2, 6), (3, 4), (5, 3)]:
        for h in range(1, hmax + 1):
            units = [a for a in range(1, p ** h) if a % p]
            e = ep(p, h)
            for c in map(F, ['1/4', '1/2', '1', '3']):
                terms = [min(x, c) if x is not None else c
                         for x in (excess(a, 1, p, h) for a in units)]
                assert sum(terms, F(0)) / e <= (h + c) / e
                count += 1
    return count


def late_block_checks():
    count = 0
    samples = []
    for p, a, delta, length in product(
            [2, 3, 5, 7], [5, 8, 13, 32],
            map(F, ['1/10', '1/2', '2']), [1, 3, 15, 50]):
        c = (delta + 3) / (a - 1)
        if c >= 1:
            continue
        roots = []
        total = F(0)
        minimum_margin = None
        for h in range(a, a + length):
            e = ep(p, h)
            m = (c.numerator * e + c.denominator - 1) // c.denominator
            slack = sum((F(mk, ep(p, k)) * (1 - F(1, p ** (h-k)))
                         for k, mk in roots), F(0))
            u = capacity(p, h, m)
            if u is not None:
                margin = u - slack - delta
                assert margin >= 1
                minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
            roots.append((h, m))
            total += F(m, e)
        assert total <= c * length + 1
        count += 1
        if p == 2 and a in [8, 32] and delta == F(1, 2) and length == 15:
            samples.append(dict(p=p, a=a, b=a+length-1, delta=str(delta),
                                cost=str(total),
                                minimum_excess_over_tolerance=str(minimum_margin)))
    return count, samples


def all_small_subset_packets():
    """All two-member subset-root packets on p=2, h=1,2,3.

Multiplicity is not needed in these finite checks. The theorem itself permits it.
"""
    p, h0, H = 2, 1, 3
    units = {h: [a for a in range(1, 2 ** h) if a % 2] for h in range(1, 4)}
    templates = []
    for masks in product(range(2), range(4), range(16)):
        roots = {}
        W = {0: F(0)}
        S = {}
        E = {}
        for h, mask in enumerate(masks, 1):
            roots[h] = [a for j, a in enumerate(units[h]) if mask & (1 << j)]
            W[h] = W[h-1] + F(len(roots[h]), ep(p, h))
            S[h] = sum((F(len(roots[k]), ep(p, k)) * (1-F(1, 2 ** (h-k)))
                        for k in range(1, h)), F(0))
            E[h] = []
            for a in units[h]:
                vals = [excess(a, b, p, h) for b in roots[h]]
                E[h].append(None if None in vals else sum(vals, F(0)))
        templates.append((roots, W, S, E))
    count = 0
    minimum = None
    delta = F(1, 4)
    for t1, t2 in product(templates, repeat=2):
        packet = [t1, t2]
        blocked = True
        for h in range(1, 4):
            for aindex in range(len(units[h])):
                es = [t[3][h][aindex] for t in packet]
                if None not in es:
                    loss = sum((max(F(0), es[i] - packet[i][2][h]) for i in range(2)), F(0))
                    if loss <= delta:
                        blocked = False
                        break
            if not blocked:
                break
            w = sum((F(len(t[0][h]), ep(p, h)) for t in packet), F(0))
            forced = h * sum((F(len(t[0][h]), ep(p, h)) / (t[2][h] + delta)
                              for t in packet), F(0)) + w
            assert forced >= 1
        if blocked:
            count += 1
            cost = sum((t[1][3] for t in packet), F(0))
            minimum = cost if minimum is None else min(minimum, cost)
    assert minimum == 2
    return dict(packets_considered=len(templates) ** 2, blocked_packets=count,
                tolerance=str(delta), minimum_cost_among_subset_packets=str(minimum))


def main():
    late_count, samples = late_block_checks()
    result = dict(
        status='all exact finite checks passed',
        greedy_shell_capacity_cases=greedy_checks(),
        capped_root_average_cases=root_average_checks(),
        late_block_constructions=late_count,
        late_block_samples=samples,
        exhaustive_small_packets=all_small_subset_packets(),
        scope='Finite exact arithmetic checks support the written proof; they do not prove the asymptotic theorem.'
    )
    out = Path(__file__).resolve().parents[1] / 'results' / 'torsion_phase_transition_checks.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
