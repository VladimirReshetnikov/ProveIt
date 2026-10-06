"""Finite exact checks for section16_contribution.tex; not a formal proof."""
from fractions import Fraction
from itertools import combinations
import json


def primes_below(n):
    return [p for p in range(2, n) if all(p % d for d in range(2, int(p**0.5)+1))]


def integer_partitions(n, lower=1):
    if n == 0:
        yield ()
    for a in range(lower, n+1):
        for rest in integer_partitions(n-a, a):
            yield (a,) + rest


localization_cases = 0
for m in range(4, 201):
    cap = m//2 + 1
    low = (2*cap+1)//3
    assert 3*low >= m and low >= 2
    for n in range(m, 1001):
        q = (n+cap-1)//cap
        small, rem = divmod(n, q)
        lengths = [small+1]*rem + [small]*(q-rem)
        assert sum(lengths) == n
        assert low <= min(lengths) <= max(lengths) <= cap
        localization_cases += 1

contained_progressions = 0
transport_cases = 0
for p in primes_below(60):
    if p < 5:
        continue
    for b in range(2, (p+1)//2+1):
        assert 2*(b-1) < p
        for start in range(b):
            for second in range(b):
                if start == second:
                    continue
                e = (second-start) % p
                vals = [start, second]
                while True:
                    u = len(vals)
                    a = second-start
                    assert all(vals[j+1]-vals[j] == a for j in range(u-1))
                    assert abs(a)*(u-1) <= b-1
                    contained_progressions += 1
                    for n in range(2*(b-1), p+1):
                        t = abs(a)
                        axes = [list(range(c, n, t)) for c in range(t)]
                        if a < 0:
                            axes = [list(reversed(axis)) for axis in axes]
                        assert min(map(len, axes)) >= u
                        assert sorted(x for axis in axes for x in axis) == list(range(n))
                        assert all(all((axis[j+1]-axis[j]) % p == e
                                       for j in range(len(axis)-1)) for axis in axes)
                        transport_cases += 1
                    new = (vals[-1]+e) % p
                    if new >= b or new in vals:
                        break
                    vals.append(new)

sampling_cases = 0
for n in range(1, 10):
    for occupied in range(n+1):
        for sizes in integer_partitions(occupied):
            q = len(sizes)
            classes = []
            cursor = 0
            for size in sizes:
                classes.append(set(range(cursor, cursor+size)))
                cursor += size
            for r in range(n+1):
                samples = list(combinations(range(n), r))
                losses = []
                for sample in samples:
                    s = set(sample)
                    hits = [len(c & s) for c in classes]
                    losses.append(sum(len(c)-h for c, h in zip(classes, hits) if h <= 1))
                actual = Fraction(sum(losses), len(losses))
                bound = Fraction(n-r) * min(Fraction(1), Fraction(2*q, r+1))
                assert actual <= bound, (n, sizes, r, actual, bound)
                if r < n:
                    extended = list(combinations(range(n), r+1))
                    capped_hits = []
                    for sample in extended:
                        s = set(sample)
                        hits = [len(c & s) for c in classes]
                        capped_hits.append(sum(h for h in hits if h <= 2))
                    add_one = Fraction(n-r, r+1)*Fraction(sum(capped_hits), len(extended))
                    assert actual == add_one
                sampling_cases += 1

assert all((2 + step) % 17 not in set(range(5)) for step in (3, -3))
print(json.dumps({
    "balanced_localization_cases": localization_cases,
    "contained_progressions": contained_progressions,
    "transport_cases": transport_cases,
    "sampling_profiles_and_sizes": sampling_cases,
    "sharp_transport_counterexample": {"p": 17, "base": [0, 3], "final": [0, 1, 2, 3, 4], "uncovered_point": [0, 2]},
    "all_checks_passed": True
}, indent=2))
