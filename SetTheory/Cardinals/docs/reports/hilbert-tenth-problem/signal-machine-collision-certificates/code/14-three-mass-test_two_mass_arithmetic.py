#!/usr/bin/env python3
"""Independent arithmetic-layer audit for the mass <= 2 CA theorem.

Standard library only. These are proof-component tests, not an enumeration of
conservative CA rules or a substitute for the theorem's mathematical proof.
"""
from itertools import product, permutations
import json
from pathlib import Path
import random


def ceildiv(a, b):
    assert b > 0
    return -((-a) // b)


def first_encounter(alpha, step, radius, pair, gap):
    """Cycle decomposition and independent per-residue affine minimization."""
    seen, states, left, right = {}, [], [], []
    control, dl, dr = pair, 0, 0
    while control not in seen:
        seen[control] = len(states)
        states.append(control)
        left.append(dl)
        right.append(dr)
        a, b = control
        dl += step[a]
        dr += step[b]
        control = alpha[a], alpha[b]
    mu = seen[control]
    period = len(states) - mu
    delta_l, delta_r = dl - left[mu], dr - right[mu]
    drift = delta_r - delta_l
    candidates = [t for t in range(mu)
                  if gap + right[t] - left[t] <= 2 * radius]
    for s in range(period):
        t = mu + s
        g = gap + right[t] - left[t]
        if g <= 2 * radius:
            k = 0
        elif drift < 0:
            k = ceildiv(g - 2 * radius, -drift)
        else:
            continue
        candidates.append(t + k * period)
    if not candidates:
        return None
    t = min(candidates)
    if t < mu:
        return t, left[t], gap + right[t], states[t]
    k, s = divmod(t - mu, period)
    i = mu + s
    return t, left[i] + k * delta_l, gap + right[i] + k * delta_r, states[i]


def stepwise_encounter(alpha, step, radius, pair, gap):
    """Raw one-step oracle; only detects a nonreturning nonnegative loop."""
    seen = {}
    a, b = pair
    left, right, t = 0, gap, 0
    while right - left > 2 * radius:
        if (a, b) in seen and right - left >= seen[a, b]:
            return None
        seen[a, b] = right - left
        left, right = left + step[a], right + step[b]
        a, b = alpha[a], alpha[b]
        t += 1
    return t, left, right, (a, b)


def feasible(lo, hi, equalities=(), forbidden=()):
    """Existence of integer k in [lo,hi], with b*k=c and affine exclusions.

    A forbidden tuple (a,b,L,U) excludes L <= a+b*k <= U.
    None as hi denotes an unbounded upper endpoint.
    """
    for b, c in equalities:
        if b == 0:
            if c != 0:
                return False
        elif c % b != 0:
            return False
        else:
            k = c // b
            lo = max(lo, k)
            hi = k if hi is None else min(hi, k)
    if hi is not None and hi < lo:
        return False
    intervals = []
    for a, b, lower, upper in forbidden:
        if lower > upper:
            continue
        if b == 0:
            if lower <= a <= upper:
                return False
            continue
        if b > 0:
            l, h = ceildiv(lower - a, b), (upper - a) // b
        else:
            l, h = ceildiv(a - upper, -b), (a - lower) // (-b)
        l = max(l, lo)
        if hi is not None:
            h = min(h, hi)
        if l <= h:
            intervals.append((l, h))
    candidate = lo
    for l, h in sorted(intervals):
        if l > candidate:
            return True
        candidate = max(candidate, h + 1)
    return hi is None or candidate <= hi


def word_occurs(particles, word, lo, hi, anchor=None):
    """One affine phase, full explicitly supplied word, absolute or translated.

    Particle triples are (state, intercept, slope), all states nonzero.
    """
    if not word:
        return hi is None or lo <= hi
    occupied = [(i, s) for i, s in enumerate(word) if s]
    if len(occupied) > len(particles):
        return False
    if anchor is None and not occupied:
        return hi is None or lo <= hi
    for assignment in permutations(range(len(particles)), len(occupied)):
        if any(particles[j][0] != s for j, (i, s) in zip(assignment, occupied)):
            continue
        equalities, forbidden = [], []
        if anchor is not None:
            for j, (i, _) in zip(assignment, occupied):
                _, a, b = particles[j]
                equalities.append((b, anchor + i - a))
            for j, (_, a, b) in enumerate(particles):
                if j not in assignment:
                    forbidden.append((a, b, anchor, anchor + len(word) - 1))
        else:
            i0, _ = occupied[0]
            _, a0, b0 = particles[assignment[0]]
            for j, (i, _) in zip(assignment[1:], occupied[1:]):
                _, a, b = particles[j]
                equalities.append((b - b0, i - i0 - a + a0))
            for j, (_, a, b) in enumerate(particles):
                if j not in assignment:
                    forbidden.append((a - a0, b - b0, -i0, len(word) - 1 - i0))
        if feasible(lo, hi, equalities, forbidden):
            return True
    return False


def exact_occurs(particles, target, lo, hi):
    if len(particles) != len(target):
        return False
    for assignment in permutations(range(len(particles))):
        if any(particles[j][0] != s for j, (u, s) in zip(assignment, target)):
            continue
        eq = [(particles[j][2], u - particles[j][1])
              for j, (u, _) in zip(assignment, target)]
        if feasible(lo, hi, eq):
            return True
    return False


def brute_word(particles, word, lo, hi, anchor=None):
    for k in range(lo, hi + 1):
        configuration = {a + b * k: s for s, a, b in particles}
        if anchor is None:
            occupied = [(i, s) for i, s in enumerate(word) if s]
            if not occupied:
                return True
            i, s = occupied[0]
            anchors = [u - i for u, state in configuration.items() if state == s]
        else:
            anchors = [anchor]
        if any(all(configuration.get(z + i, 0) == s for i, s in enumerate(word))
               for z in anchors):
            return True
    return False


def run():
    rng = random.Random(20261002)
    counts = {"exhaustive_encounter_cases": 0, "random_encounter_cases": 0,
              "anchored_word_cases": 0, "unanchored_word_cases": 0,
              "exact_configuration_cases": 0, "large_integer_cases": 0}
    for r in (0, 1, 2):
        for m in (1, 2):
            for alpha in product(range(m), repeat=m):
                for step in product(range(-r, r + 1), repeat=m):
                    for pair in product(range(m), repeat=2):
                        for gap in range(2 * r + 1, 2 * r + 25):
                            actual = first_encounter(alpha, step, r, pair, gap)
                            expected = stepwise_encounter(alpha, step, r, pair, gap)
                            assert actual == expected, (r, alpha, step, pair, gap, actual, expected)
                            if actual:
                                assert 1 <= actual[2] - actual[1] <= 2 * r
                            counts["exhaustive_encounter_cases"] += 1
    for _ in range(20000):
        m, r = rng.randrange(1, 9), rng.randrange(0, 5)
        alpha = tuple(rng.randrange(m) for _ in range(m))
        step = tuple(rng.randrange(-r, r + 1) for _ in range(m))
        pair = rng.randrange(m), rng.randrange(m)
        gap = rng.randrange(2 * r + 1, 2 * r + 500)
        actual = first_encounter(alpha, step, r, pair, gap)
        expected = stepwise_encounter(alpha, step, r, pair, gap)
        assert actual == expected, (r, alpha, step, pair, gap, actual, expected)
        counts["random_encounter_cases"] += 1
    for _ in range(20000):
        lo, hi = rng.randrange(0, 5), rng.randrange(5, 16)
        m = rng.randrange(3)
        slopes = [rng.randrange(-2, 3) for _ in range(m)]
        intercepts = [rng.randrange(-30, 31)] if m else []
        if m == 2:
            intercepts.append(intercepts[0] + abs(slopes[1] - slopes[0]) * hi + rng.randrange(1, 10))
        particles = [(rng.randrange(1, 4), a, b) for a, b in zip(intercepts, slopes)]
        sample = rng.randrange(lo, hi + 1)
        configuration = {a + b * sample: s for s, a, b in particles}
        n = rng.randrange(0, 12)
        anchor = rng.randrange(-40, 41)
        if particles and rng.randrange(2):
            anchor = rng.choice(list(configuration)) - rng.randrange(max(1, n))
        word = tuple(configuration.get(anchor + i, 0) for i in range(n))
        if n and rng.randrange(2):
            word = list(word)
            word[rng.randrange(n)] = rng.randrange(4)
            word = tuple(word)
        assert word_occurs(particles, word, lo, hi, anchor) == brute_word(particles, word, lo, hi, anchor)
        counts["anchored_word_cases"] += 1
        assert word_occurs(particles, word, lo, hi) == brute_word(particles, word, lo, hi)
        counts["unanchored_word_cases"] += 1
        target = sorted(configuration.items())
        if target and rng.randrange(2):
            index = rng.randrange(len(target))
            u, state = target[index]
            target[index] = (u + rng.randrange(-3, 4), rng.randrange(1, 4))
            target = sorted(dict(target).items())
        expected = any(sorted((a + b * k, s) for s, a, b in particles) == target
                       for k in range(lo, hi + 1))
        assert exact_occurs(particles, target, lo, hi) == expected
        counts["exact_configuration_cases"] += 1
    huge = 2 ** 1000
    assert first_encounter((0, 1), (1, -1), 1, (0, 1), huge) == (huge // 2 - 1, huge // 2 - 1, huge // 2 + 1, (0, 1))
    counts["large_integer_cases"] += 1
    # The query lies in the interior of a huge free flight, before any encounter.
    assert word_occurs([(1, 0, 1), (2, huge, -1)], (1,), 0, huge // 2 - 2, huge // 4)
    counts["large_integer_cases"] += 1
    assert not word_occurs([(1, 0, 1), (2, huge, -1)], (1, 2), 0, huge // 2 - 2, huge // 2 - 1)
    counts["large_integer_cases"] += 1
    assert word_occurs([(1, 0, 2)], (1,), 0, None, huge)
    counts["large_integer_cases"] += 1
    assert not word_occurs([(1, 0, 2)], (1,), 0, None, huge + 1)
    counts["large_integer_cases"] += 1
    assert word_occurs([(1, huge, 0)], (0,), 0, None, 0)
    counts["large_integer_cases"] += 1
    assert not word_occurs([(1, huge, 0)], (0,), 0, None, huge)
    counts["large_integer_cases"] += 1
    receipt = {"status": "PASS", "seed": 20261002, "counts": counts,
               "total_cases": sum(counts.values()),
               "scope": "Independent encounter acceleration and affine-phase observation arithmetic; not a complete CA implementation or literature novelty check."}
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    run()
