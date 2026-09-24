#!/usr/bin/env python3
"""Deterministic stress tests for the proposed ordinal-sum formula.

Run: python3 code/verify.py --output checks/results.json
These are exact symbolic consistency tests, not a proof of the theorem.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations_with_replacement
import json
from pathlib import Path
import random
from time import perf_counter
from ordinals import (Ordinal, ZERO, ONE, OMEGA, finite, omega_power,
                      natural_sum, chi, constant_value, base, weight, Profile)


def build_basis() -> list[Ordinal]:
    """Include successor/limit exponents and long prefixes; no truncation."""
    exponents = [finite(n) for n in range(1, 5)] + [
        OMEGA, OMEGA + ONE, OMEGA + finite(2),
        OMEGA.natural_times_finite(2), omega_power(finite(2)),
        omega_power(OMEGA)]
    values = {finite(n) for n in range(7)}
    for exponent in exponents:
        for coefficient in [1, 2, 3]:
            for n in [0, 1, 2, 5]:
                values.add(omega_power(exponent, coefficient) + finite(n))
    for top_exp in [finite(2), finite(3), OMEGA, OMEGA + ONE,
                    omega_power(finite(2)), omega_power(OMEGA)]:
        for last_exp in [ONE, finite(2), OMEGA, OMEGA + ONE]:
            if last_exp < top_exp:
                for coefficient in [1, 2]:
                    for n in [0, 1, 3]:
                        values.add(omega_power(top_exp) + omega_power(last_exp, coefficient) + finite(n))
    return sorted(values)


def run_tests(seed: int, samples: int) -> dict:
    started = perf_counter()
    rng = random.Random(seed)
    counts = Counter()
    values = build_basis()
    positive = values[1:]

    # Arithmetic is separately checked before testing the research formula.
    for a in values:
        assert a + ZERO == a == ZERO + a
        assert a.natural_sum(ZERO) == a
        assert a.natural_times_omega().natural_sum(OMEGA) == (a + ONE).natural_times_omega()
        counts['arithmetic_boundary_checks'] += 3
        for b in values:
            ns = a.natural_sum(b)
            assert ns == b.natural_sum(a)
            assert a + b <= ns
            counts['arithmetic_pair_checks'] += 2
            if a <= b:
                assert a + a.right_remainder(b) == b
                counts['remainder_checks'] += 1
    for _ in range(samples):
        a, b, c = (rng.choice(values) for _ in range(3))
        assert (a + b) + c == a + (b + c)
        assert a.natural_sum(b).natural_sum(c) == a.natural_sum(b.natural_sum(c))
        counts['arithmetic_triple_checks'] += 2
        lo, mid, hi = sorted((a, b, c))
        assert lo.right_remainder(mid) + mid.right_remainder(hi) == lo.right_remainder(hi)
        counts['remainder_cocycle_checks'] += 1

    # Central absorption lemma, exhaustive on this finite basis and m=0,...,8.
    for t in positive:
        for e in positive:
            if e > t:
                break
            for m in range(9):
                lhs = base(e).natural_sum(weight(e, t).natural_times_finite(m))
                assert lhs < constant_value(t), ('absorption', str(e), str(t), m, str(lhs))
                counts['absorption_general_checks'] += 1
                if t.is_limit and e < t:
                    assert lhs < t.natural_times_omega(), ('limit absorption', str(e), str(t), m)
                    counts['absorption_limit_checks'] += 1

    # Verify profile corrections and identities on independently chosen heads.
    profiles = []
    for _ in range(samples):
        e = rng.choice(positive)
        choices = [a for a in values if a >= e]
        heads = tuple(rng.choice(choices) for _ in range(rng.randrange(7)))
        p = Profile(e, heads)
        u, s = p.value(), p.lipparini_S()
        assert s <= u <= s.natural_sum(OMEGA)
        if e.is_successor:
            assert u == s.natural_sum(OMEGA if chi(e.predecessor()) else ZERO)
        elif e.terms[-1][0].is_successor:
            k = sum(a < e + OMEGA for a in heads)
            assert u == s + finite(k)
        else:
            assert u == s
        counts['profile_correction_checks'] += 1
        profiles.append(p)
        # Force an actual larger profile: increase the cut and preserve all
        # heads that lie above the new cut, then increase/add some heads.
        f = rng.choice([a for a in positive if a >= e])
        new_heads = []
        for a in heads:
            if a >= f:
                new_heads.append(rng.choice([b for b in values if b >= a]))
        for _ in range(rng.randrange(4)):
            new_heads.append(rng.choice([a for a in values if a >= f]))
        q = Profile(f, tuple(new_heads))
        assert p.le(q)
        assert u <= q.value()
        if p != q:
            assert u < q.value(), ('profile strictness', str(p), str(q), str(u), str(q.value()))
            counts['forced_strict_profile_checks'] += 1
        else:
            counts['equal_profile_checks'] += 1

    # Exhaustive small profiles: a different mix of finite and transfinite cuts.
    small = [finite(1), finite(2), finite(3), OMEGA, OMEGA + ONE,
             OMEGA + finite(2), omega_power(finite(2)), omega_power(OMEGA),
             omega_power(OMEGA) + ONE, omega_power(OMEGA + ONE)]
    small_profiles = []
    for e in small:
        choices = [a for a in small if a >= e]
        for size in range(4):
            for heads in combinations_with_replacement(choices, size):
                small_profiles.append(Profile(e, heads))
    cached = {p: p.value() for p in small_profiles}
    for p in small_profiles:
        for q in small_profiles:
            if p.le(q):
                assert cached[p] <= cached[q]
                if p != q:
                    assert cached[p] < cached[q], (str(p), str(q))
                counts['exhaustive_comparable_profile_pairs'] += 1

    # Independent finite-poset rank calculation.  The topological ordering
    # uses cut and unshifted integer head-sum, not the asserted rank formula.
    finite_caps = []
    for maximum in range(1, 6):
        for cap in range(5):
            states = []
            for z in range(maximum + 1):
                for size in range(cap + 1):
                    for entries in combinations_with_replacement(range(z + 1, maximum + 1), size):
                        states.append(Profile(finite(z + 1), tuple(map(finite, entries))))
            states.sort(key=lambda p: (p.cut.finite_part, sum(a.finite_part for a in p.heads)))
            ranks = {}
            for p in states:
                rank = max((r + 1 for q, r in ranks.items() if q.le(p)), default=0)
                z = p.cut.finite_part - 1
                expected = z * (cap + 1) + sum(a.finite_part - z for a in p.heads)
                assert rank == expected, ('finite rank', maximum, cap, str(p), rank, expected)
                ranks[p] = rank
                counts['independent_finite_rank_checks'] += 1
            top = Profile(finite(maximum + 1))
            finite_caps.append({'maximum_entry': maximum, 'head_cap': cap,
                                'states': len(states), 'computed_top_rank': ranks[top]})

    # Regression examples, including each case distinction and a subtle +1.
    w2, ww = omega_power(finite(2)), omega_power(OMEGA)
    cases = [
        ('zero sequence', Profile(ONE), ZERO),
        ('one finite head over zero tail', Profile(ONE, (finite(5),)), finite(5)),
        ('cofinal natural tail', Profile(OMEGA), w2),
        ('one omega over cofinal natural tail', Profile(OMEGA, (OMEGA,)), w2 + ONE),
        ('two omega heads over cofinal natural tail', Profile(OMEGA, (OMEGA, OMEGA)), w2 + finite(2)),
        ('constant omega', Profile(OMEGA + ONE), w2 + OMEGA),
        ('constant omega+1', Profile(OMEGA + finite(2)), w2 + OMEGA.natural_times_finite(2)),
        ('omega+5 head over cofinal natural tail', Profile(OMEGA, (OMEGA + finite(5),)), w2 + finite(6)),
        ('omega*2+3 head over cofinal natural tail', Profile(OMEGA, (OMEGA.natural_times_finite(2) + finite(3),)), w2 + OMEGA + finite(3)),
        ('cofinal tail below omega^omega', Profile(ww), ww),
        ('one omega^omega at that limit cut', Profile(ww, (ww,)), ww.natural_times_finite(2)),
        ('constant omega^omega', Profile(ww + ONE), omega_power(OMEGA + ONE)),
        ('constant omega^(omega+1)', Profile(omega_power(OMEGA + ONE) + ONE), omega_power(OMEGA + finite(2)) + OMEGA),
    ]
    regressions = []
    for name, p, expected in cases:
        actual = p.value()
        assert actual == expected, (name, str(actual), str(expected))
        counts['explicit_regressions'] += 1
        regressions.append({'example': name, 'profile': str(p), 'N': str(actual),
                            'S': str(p.lipparini_S())})

    return {'status': 'PASS', 'seed': seed, 'random_samples': samples,
            'ordinal_basis_size': len(values), 'small_profile_count': len(small_profiles),
            'checks': dict(counts), 'total_counted_checks': sum(counts.values()),
            'seconds': round(perf_counter() - started, 3),
            'regressions': regressions, 'finite_cap_rank_checks': finite_caps,
            'limitations': ['Finite exact tests are not a proof.',
                            'All represented ordinals are below epsilon_0.',
                            'No computation here determines the cut of an arbitrary infinite sequence.',
                            'The rank minimality argument is checked in prose, not by these inequalities.']}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=20260919)
    parser.add_argument('--samples', type=int, default=10000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.samples < 0:
        parser.error('--samples must be nonnegative')
    result = run_tests(args.seed, args.samples)
    text = json.dumps(result, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
