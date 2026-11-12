"""Independent named-variable normalization audit.

The oracle is adapted from ProveIt, pinned commit
8fa5ade009b5cceba7b68f07b6a834fe77cf10c1,
Research/parameter_intro/code/audit.py, under the repository MIT-0 license.
It is verification support, never imported by the acceptance checker.
"""
from pathlib import Path
import itertools
import json
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
import checker
primary = {'walk': checker.walk, 'sub': checker.sub}
names = itertools.count()


def decode(a, bound=(), form=False):
    if type(a) is int:
        assert not form
        if a == 0:
            return ('zero',)
        if a < 0:
            return ('free', a)
        return ('var', bound[a - 1])
    assert type(a) is list
    if form:
        if len(a) == 2:
            return ('eq', decode(a[0], bound), decode(a[1], bound))
        assert len(a) == 1
        x, y = next(names), next(names)
        return ('d', x, y, decode(a[0], (y, x) + bound, True))
    assert len(a) == 3
    counter, state = next(names), next(names)
    return ('r', decode(a[0], bound), decode(a[1], bound), counter, state,
            decode(a[2], (state, counter) + bound))


def replace(a, mapping):
    tag = a[0]
    if tag == 'var':
        return mapping.get(a[1], a)
    if tag in ('zero', 'free'):
        return a
    if tag == 's':
        return ('s', replace(a[1], mapping))
    if tag == 'r':
        return ('r', replace(a[1], mapping), replace(a[2], mapping),
                a[3], a[4], replace(a[5], {k: v for k, v in mapping.items() if k not in (a[3], a[4])}))
    if tag == 'eq':
        return ('eq', replace(a[1], mapping), replace(a[2], mapping))
    return ('d', a[1], a[2], replace(a[3], {k: v for k, v in mapping.items() if k not in (a[1], a[2])}))


def normal(a):
    tag = a[0]
    if tag in ('zero', 'free', 'var'):
        return a
    if tag == 's':
        return ('s', normal(a[1]))
    if tag == 'eq':
        return ('eq', normal(a[1]), normal(a[2]))
    if tag == 'd':
        return ('d', a[1], a[2], normal(a[3]))
    c, seed, h = normal(a[1]), normal(a[2]), normal(a[5])
    if c[0] == 'zero':
        return ('s', seed)
    if c[0] == 's':
        previous = normal(('r', c[1], seed, a[3], a[4], h))
        return normal(replace(h, {a[3]: c[1], a[4]: previous}))
    return ('r', c, seed, a[3], a[4], h)


def encode(a, bound=()):
    tag = a[0]
    if tag == 'zero':
        return 0
    if tag == 'free':
        return a[1]
    if tag == 'var':
        return bound.index(a[1]) + 1
    if tag == 's':
        return [0, encode(a[1], bound), 0]
    if tag == 'eq':
        return [encode(a[1], bound), encode(a[2], bound)]
    if tag == 'd':
        return [encode(a[3], (a[2], a[1]) + bound)]
    return [encode(a[1], bound), encode(a[2], bound),
            encode(a[5], (a[4], a[3]) + bound)]


def random_term(rng, size, depth):
    leaves = [0, -1, -2] + list(range(1, depth + 1))
    if size == 0 or rng.randrange(3) == 0:
        return rng.choice(leaves)
    if rng.randrange(3) == 0:
        return [0, random_term(rng, size - 1, depth), 0]
    # Literal zero/one or a parameter keeps numeric experiments inexpensive.
    c = rng.choice(leaves + [[0, 0, 0]])
    return [c, random_term(rng, size - 1, depth),
            random_term(rng, size - 1, depth + 2)]


def numeric(a, free, bound=()):
    if type(a) is int:
        return 0 if a == 0 else free[a] if a < 0 else bound[a - 1]
    counter = numeric(a[0], free, bound)
    state = numeric(a[1], free, bound) + 1
    for index in range(counter):
        state = numeric(a[2], free, (state, index) + bound)
    return state


def normalization_audit():
    rng = random.Random(11814771)
    counts = dict(normal_forms=0, numerical_values=0, openings=0,
                  successor_contractions=0, capture_controls=0)
    for depth in range(4):
        outer = tuple(next(names) for _ in range(depth))
        for _ in range(100):
            a = random_term(rng, 3, depth)
            expected = encode(normal(decode(a, outer)), outer)
            actual = primary['walk'](a, lambda i, d: i)
            assert actual == expected, (a, actual, expected)
            counts['normal_forms'] += 1
            for _ in range(3):
                values = tuple(rng.randrange(3) for _ in outer)
                free = {-1: rng.randrange(3), -2: rng.randrange(3)}
                assert numeric(a, free, values) == numeric(actual, free, values)
                counts['numerical_values'] += 1
        for protected in range(2):
            prefix = tuple(next(names) for _ in range(protected))
            target = next(names)
            for _ in range(60):
                a = random_term(rng, 2, depth + protected + 1)
                t = random_term(rng, 2, depth)
                named = decode(a, prefix + (target,) + outer)
                image = decode(t, outer)
                expected = encode(normal(replace(named, {target: image})), prefix + outer)
                actual = primary['sub'](a, t, protected)
                assert actual == expected, (a, t, protected, actual, expected)
                counts['openings'] += 1
        for _ in range(80):
            c = random_term(rng, 1, depth)
            seed = random_term(rng, 1, depth)
            h = random_term(rng, 2, depth + 2)
            a = [[0, c, 0], seed, h]
            expected = encode(normal(decode(a, outer)), outer)
            assert primary['walk'](a, lambda i, d: i) == expected, (depth, a, primary['walk'](a, lambda i, d: i), expected)
            counts['successor_contractions'] += 1
    # State-first opening without a lift would confuse the outer counter/state.
    raw = [-1, 0, [[0, 2, 0], 0, 1]]
    expected = [-1, 0, [2, 0, 1]]
    assert primary['walk'](raw, lambda i, d: i) == expected
    counts['capture_controls'] += 1
    # The predecessor equation is a literal normalization identity.
    assert primary['walk']([[0, -1, 0], 0, 2], lambda i, d: i) == -1
    counts['capture_controls'] += 1
    return counts

if __name__ == '__main__':
    result = normalization_audit()
    result['scope'] = 'Finite comparison with an independent named-variable normalizer; not a universal proof.'
    (ROOT / 'evidence' / 'normalization_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
