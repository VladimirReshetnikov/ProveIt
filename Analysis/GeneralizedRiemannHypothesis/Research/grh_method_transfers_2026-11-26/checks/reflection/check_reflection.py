"""Verify the symmetric-group local character inequalities with exact arithmetic."""
from collections import Counter, deque
from fractions import Fraction
from itertools import permutations
from math import factorial, gcd, prod
import json
from pathlib import Path


def compose(left, right):
    return tuple(left[i] for i in right)


def cycle_type(p):
    seen = set()
    parts = []
    for i in range(len(p)):
        if i in seen:
            continue
        length = 0
        while i not in seen:
            seen.add(i)
            i = p[i]
            length += 1
        parts.append(length)
    return tuple(sorted(parts))


def perm_from_cycles(n, cycles):
    p = list(range(n))
    support = []
    for cycle in cycles:
        support.extend(cycle)
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            assert 1 <= a <= n and 1 <= b <= n
            p[a-1] = b-1
    assert len(support) == len(set(support))
    return tuple(p)


def partitions(n, smallest=1):
    if n == 0:
        yield ()
    for first in range(smallest, n+1):
        for tail in partitions(n-first, first):
            yield (first,) + tail


def moebius(n):
    if n == 1:
        return 1
    return -sum(moebius(i) for i in range(1, n) if n % i == 0)


def normalized_trace(d, j):
    # Ramanujan's sum c_d(j) = sum_{k|gcd(d,j)} k mu(d/k).
    common = gcd(d, j)
    value = sum(k*moebius(d//k) for k in range(1, common+1) if common % k == 0)
    phi = sum(gcd(d, k) == 1 for k in range(1, d+1))
    return Fraction(value, phi)


def class_sizes(n):
    return {t: factorial(n)//prod(j**m * factorial(m) for j, m in Counter(t).items())
            for t in partitions(n)}


def symmetric_block_row(n, d, generators):
    """Recognize a full symmetric block, optionally with a second block exchanged."""
    if d != 2:
        return None
    identity = tuple(range(n))
    gen = {}
    for g, j in generators:
        if g in gen:
            assert gen[g] == j
        gen[g] = j
    if identity in gen:
        assert gen.pop(identity) == 0
    for start in range(n):
        for width in range(3, n - start + 1):
            letters = list(range(start+1, start+width+1))
            cycle = perm_from_cycles(n, [letters])
            transposition = perm_from_cycles(n, [letters[:2]])
            if cycle not in gen or transposition not in gen:
                continue
            k = gen[transposition]
            if gen[cycle] != k*((width-1) % 2):
                continue
            extra = set(gen) - {cycle, transposition}
            fixed = n - width
            sizes = class_sizes(width)
            values = {t: c*(-1)**(k*(width-len(t))) for t, c in sizes.items()}
            if not extra:
                return {tuple(sorted((1,)*fixed + t)): x for t, x in values.items()}
            if start + 2*width > n:
                continue
            flip = perm_from_cycles(n, [[i, i+width] for i in letters])
            if extra != {flip}:
                continue
            # The two block generators give S_width, and the flip conjugates
            # it to the disjoint second copy. Thus H=(S_width x S_width):C2.
            fixed = (1,)*(n-2*width)
            out = Counter()
            for a, va in values.items():
                for b, vb in values.items():
                    out[tuple(sorted(fixed + a + b))] += va*vb
                # In the other coset a cycle of the product has doubled length.
                out[tuple(sorted(fixed+tuple(2*i for i in a)))] += (
                    (-1)**gen[flip] * factorial(width) * va)
            return out
    return None


def row_from_generators(n, data, types):
    d = data['d']
    generators = [(perm_from_cycles(n, cycles), i) for cycles, i in data['generators']]
    fast = symmetric_block_row(n, d, generators) if n >= 10 else None
    if fast is not None:
        return [fast.get(t, 0) for t in types]
    identity = tuple(range(n))
    image = {identity: 0}
    todo = deque([identity])
    while todo:
        g = todo.popleft()
        for h, j in generators:
            k = compose(g, h)
            exponent = (image[g] + j) % d
            if k in image:
                assert image[k] == exponent, 'inconsistent cyclic character'
            else:
                image[k] = exponent
                todo.append(k)
    assert set(image.values()) == set(range(d))
    # Average of all Galois conjugates of exp(2 pi i j/d).
    traces = [normalized_trace(d, j) for j in range(d)]
    by_type = Counter()
    for g, j in image.items():
        by_type[cycle_type(g)] += traces[j]
    return [by_type[t] for t in types]


def check(n, cert):
    types = list(partitions(n))
    count = class_sizes(n)
    assert sum(count.values()) == factorial(n)
    if n <= 7:
        assert count == Counter(cycle_type(p) for p in permutations(range(n)))
    linear = Fraction(-2, (n-1)*factorial(n))
    assert [Fraction(x) for x in cert['eq']] == [linear, 0]
    combined = [linear*count[t] for t in types]
    for term in cert['rows']:
        coefficients = row_from_generators(n, term, types)
        assert coefficients == [Fraction(x) for x in term['row']]
        weight = Fraction(term['weight'])
        assert weight > 0
        combined = [a + weight*b for a, b in zip(combined, coefficients)]
    expected = [Fraction(n-3, n-1) if t == (1,)*n else -1
                if t == (1,)*(n-2) + (2,) else 0 for t in types]
    assert combined == expected
    # The standard representation character is number of fixed points minus one.
    standard = [t.count(1)-1 for t in types]
    assert sum(x*y for x, y in zip(combined, standard)) == 0
    assert all(sum(Fraction(a)*b for a, b in zip(term['row'], standard)) == 0 for term in cert['rows'])
    print(f'S{n}: {len(types)} conjugacy classes, {len(cert["rows"])} subgroup rows, '
          f'exact identity and equality witness verified. Optimal constant = {n-1}.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every exact check is active.')
    source = Path(__file__).with_name('certificates.json')
    for n, certificate in json.loads(source.read_text()).items():
        check(int(n), certificate)
