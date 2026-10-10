"""Exact word algebra for one-variable multiple polylogarithms.

Conventions: outer letter first, omega_0=dt/t, omega_1=dt/(1-t).
The word 0011 represents Li_{3,1}(z,1).  All coefficients are exact.
No numerical relation search is used.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd
from typing import Iterable

Word = tuple[int, ...]
NormalKey = tuple[int, Word]  # power of log(q), word ending in 1 (or empty)
ReductionKey = tuple[int, tuple[int, ...], tuple[int, ...]]


def validate_word(word: Word) -> None:
    if any(x not in (0, 1) for x in word):
        raise ValueError('The alphabet is {0,1}.')


@lru_cache(None)
def shuffle(u: Word, v: Word) -> dict[Word, int]:
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    out: Counter[Word] = Counter()
    for tail, n in shuffle(u[1:], v).items():
        out[(u[0],) + tail] += n
    for tail, n in shuffle(u, v[1:]).items():
        out[(v[0],) + tail] += n
    return dict(out)


def shuffle_many(words: Iterable[Word]) -> dict[Word, int]:
    out: dict[Word, int] = {(): 1}
    for word in words:
        new: Counter[Word] = Counter()
        for u, c in out.items():
            for v, d in shuffle(u, word).items():
                new[v] += c * d
        out = dict(new)
    return out


@lru_cache(None)
def normalize_trailing_zeros(word: Word) -> dict[NormalKey, Fraction]:
    """Express H_word(q) in log(q)^j times ordinary MPLs.

    Eliminate the trailing zero using H_v H_0=H_{v shuffle 0}.
    The pivot multiplicity is the number of trailing zeros in word.
    """
    validate_word(word)
    if not word or word[-1] == 1:
        return {(0, word): Fraction(1)}
    v = word[:-1]
    terms = shuffle(v, (0,))
    pivot = terms[word]
    out: defaultdict[NormalKey, Fraction] = defaultdict(Fraction)
    for (j, u), c in normalize_trailing_zeros(v).items():
        out[(j + 1, u)] += c / pivot
    for other, mult in terms.items():
        if other == word:
            continue
        for key, c in normalize_trailing_zeros(other).items():
            out[key] -= Fraction(mult, pivot) * c
    return {k: v for k, v in out.items() if v}


def word_to_indices(word: Word) -> tuple[int, ...]:
    if word and word[-1] != 1:
        raise ValueError('A polylogarithm word must end in 1.')
    indices, zeros = [], 0
    for letter in word:
        if letter == 0:
            zeros += 1
        else:
            indices.append(zeros + 1)
            zeros = 0
    return tuple(indices)


def indices_to_word(indices: tuple[int, ...]) -> Word:
    if any(s < 1 for s in indices):
        raise ValueError('Indices must be positive integers.')
    return tuple(t for s in indices for t in (0,) * (s - 1) + (1,))


@lru_cache(None)
def endpoint(word: Word) -> dict[tuple[int, ...], Fraction]:
    """H_word(1), for the convergent endpoint words used below.

    Nonempty input begins in 0.  Terms with a positive log(1) power vanish.
    """
    if word and word[0] != 0:
        raise ValueError('Endpoint convergence requires initial letter 0.')
    out: defaultdict[tuple[int, ...], Fraction] = defaultdict(Fraction)
    for (j, u), c in normalize_trailing_zeros(word).items():
        if j == 0:
            indices = word_to_indices(u)
            if indices and indices[0] < 2:
                raise AssertionError('Divergent endpoint produced.')
            out[indices] += c
    return {k: v for k, v in out.items() if v}


@lru_cache(None)
def complement_reduce(word: Word) -> dict[ReductionKey, Fraction]:
    """At q=1/(1-z), reduce H_word(z) by complementary depth.

    Output (j, S, T): c means c*log(q)^j*Li_S(q,1,...)*zeta(T).
    Empty S or T denotes 1, not a polylogarithm/zeta of weight zero.
    Every term has len(S)+len(T) <= number of zeros in the input.
    """
    validate_word(word)
    if not word or word[-1] != 1:
        raise ValueError('Input must be nonempty and end in 1.')
    positions = [i for i, x in enumerate(word) if x == 0]
    sign = (-1) ** len(positions)
    out: defaultdict[ReductionKey, Fraction] = defaultdict(Fraction)
    for choices in product((0, 1), repeat=len(positions)):
        transformed = [0] * len(word)
        for p, x in zip(positions, choices):
            transformed[p] = x
        transformed = tuple(transformed)
        for split in range(len(word) + 1):
            prefix, suffix = transformed[:split], transformed[split:]
            left = normalize_trailing_zeros(prefix)
            right = endpoint(tuple(reversed(suffix)))
            coefficient = sign * (-1) ** len(suffix)
            for (j, u), a in left.items():
                S = word_to_indices(u)
                for T, b in right.items():
                    out[(j, S, T)] += coefficient * a * b
    out = {k: c for k, c in out.items() if c}
    for (j, S, T), c in out.items():
        assert j + sum(S) + sum(T) == len(word)
        assert len(S) + len(T) <= len(positions)
    return out


def one_zero_formula(a: int, b: int) -> dict[ReductionKey, Fraction]:
    """Independent finite formula from a single logarithmic integral."""
    if a < 0 or b < 0:
        raise ValueError('a,b must be nonnegative.')
    out: defaultdict[ReductionKey, Fraction] = defaultdict(Fraction)
    for j in range(a + 1):
        r = b + j + 1
        c = Fraction((-1) ** j * comb(b + j + 1, j), factorial(a - j))
        for k in range(1, r + 2):
            out[(a - j + r + 1 - k, (k,), ())] += c * Fraction((-1) ** k, factorial(r + 1 - k))
        out[(a - j, (), (r + 1,))] += c * (-1) ** r
        out[(a - j + r + 1, (), ())] -= c / factorial(r + 1)
    return {k: c for k, c in out.items() if c}


def is_lyndon(word: Word) -> bool:
    return bool(word) and all(word < word[j:] for j in range(1, len(word)))


def lyndon_factorization(word: Word) -> tuple[Word, ...]:
    """Duval factorization into nonincreasing Lyndon words."""
    factors = []
    i, n = 0, len(word)
    while i < n:
        j, k = i + 1, i
        while j < n and word[k] <= word[j]:
            k = i if word[k] < word[j] else k + 1
            j += 1
        length = j - k
        while i <= k:
            factors.append(word[i:i + length])
            i += length
    assert tuple(x for f in factors for x in f) == word
    assert all(is_lyndon(f) for f in factors)
    assert all(factors[i] >= factors[i + 1] for i in range(len(factors) - 1))
    return tuple(factors)


def mobius(n: int) -> int:
    if n < 1:
        raise ValueError('Positive n required.')
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        sign = -sign
    return sign


def lyndon_count(weight: int, depth: int) -> int:
    if not 1 <= depth <= weight:
        return 0
    g = gcd(weight, depth)
    total = sum(mobius(k) * comb(weight // k, depth // k)
                for k in range(1, g + 1) if g % k == 0)
    assert total % weight == 0
    return total // weight


def admissible_words(weight: int, depth: int | None = None):
    if weight < 1:
        return
    for prefix in product((0, 1), repeat=weight - 1):
        w = prefix + (1,)
        if depth is None or sum(w) == depth:
            yield w


def latex_reduction(terms: dict[ReductionKey, Fraction]) -> str:
    parts = []
    for (j, S, T), c in sorted(terms.items(), reverse=True):
        factors = []
        if j:
            factors.append('L' if j == 1 else f'L^{{{j}}}')
        if S:
            sub = ','.join(map(str, S))
            factors.append(r'\Li_{' + sub + '}(q)')
        if T:
            factors.append(r'\zeta(' + ','.join(map(str, T)) + ')')
        v = abs(c)
        coef = '' if v == 1 and factors else (str(v.numerator) if v.denominator == 1 else rf'\frac{{{v.numerator}}}{{{v.denominator}}}')
        term = coef + ' '.join(factors)
        if parts:
            parts.append((' + ' if c > 0 else ' - ') + term)
        else:
            parts.append(('-' if c < 0 else '') + term)
    return ''.join(parts) or '0'


def two_zero_height_one(weight: int) -> dict[ReductionKey, Fraction]:
    """Closed finite formula for Li_{3,1^(weight-3)}(z), weight>=3."""
    if weight < 3:
        raise ValueError('weight must be >= 3')
    w = weight
    out: defaultdict[ReductionKey, Fraction] = defaultdict(Fraction)
    out[(w, (), ())] += Fraction(1, factorial(w))
    for k in range(1, w + 1):
        out[(w-k, (k,), ())] += Fraction((-1)**k * (k-2), factorial(w-k))
        for a in range(1, k):
            out[(w-k, (a, k-a), ())] += Fraction((-1)**k, factorial(w-k))
    sign = (-1)**(w-1)
    out[(1, (), (w-1,))] += sign
    out[(0, (1,), (w-1,))] += sign
    out[(0, (), (w,))] += sign*(w-2)
    out[(0, (), (w-1, 1))] -= sign
    return {k: c for k, c in out.items() if c}


if __name__ == '__main__':
    for S in [(2,1,1), (1,2,1), (1,1,2), (3,1,1), (2,2,1), (3,1,1,1)]:
        red = complement_reduce(indices_to_word(S))
        print(S, latex_reduction(red))
