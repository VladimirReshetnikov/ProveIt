"""Ordinal arithmetic on hereditary Cantor normal forms below epsilon_0.

A term is a tuple of terms in nonincreasing order.  Repetition encodes
coefficients.  Python's lexicographic order on these tuples is the notation
order.  The public arithmetic operations expect canonical inputs.
"""
from itertools import groupby, product


ZERO = ()
ONE = (ZERO,)
OMEGA = (ONE,)


def W(exponent):
    """The single monomial omega**exponent."""
    return (exponent,)


def nat(n):
    """Embed a nonnegative Python integer as a term."""
    if n < 0:
        raise ValueError("expected a nonnegative integer")
    return (ZERO,) * n


def succ(a):
    return a + ONE


def add(a, b):
    if not b:
        return a
    cut = len(a)
    while cut and a[cut - 1] < b[0]:
        cut -= 1
    return a[:cut] + b


def mul(a, b):
    if not a or not b:
        return ZERO
    # Positive-exponent blocks are single monomials. Zero-exponent
    # blocks add copies of a, with the usual truncation in each sum.
    positive = []
    for i, exponent in enumerate(b):
        if exponent:
            positive.append(add(a[0], exponent))
        else:
            leading = a[0]
            same = 0
            while same < len(a) and a[same] == leading:
                same += 1
            copies = len(b) - i
            return tuple(positive) + (leading,) * (same * (copies - 1)) + a
    return tuple(positive)


def divomega(b):
    """Return q,n with b = omega*q + n and n a nonnegative integer."""
    quotient = []
    for i, exponent in enumerate(b):
        if not exponent:
            return tuple(quotient), len(b) - i
        # Invert 1+d=e. Finite positive e loses one zero. Infinite e
        # absorbs the 1 and therefore is its own inverse image.
        quotient.append(exponent if exponent[0] else exponent[1:])
    return tuple(quotient), 0


def finite_power(a, n):
    if n < 0:
        raise ValueError("expected a nonnegative integer")
    result = ONE
    for _ in range(n):
        result = mul(result, a)
    return result


def growth(a):
    """The exponent in a**omega = omega**growth(a), for a >= 2."""
    if a <= ONE:
        raise ValueError("growth requires a base of at least two")
    return mul(a[0], OMEGA) if a[0] else ONE


def power(a, b):
    if not b or a == ONE:
        return ONE
    if not a:
        return ZERO
    q, n = divomega(b)
    return mul(W(mul(growth(a), q)), finite_power(a, n))


def _finite_factors(n):
    factors = []
    divisor = 2
    while n > 1:
        if n % divisor == 0:
            factors.append(nat(divisor))
            n //= divisor
        else:
            divisor += 1
    return reversed(factors)


def prime_factors(a):
    """Return the unique ordered factorization into ordinal primes."""
    if not a:
        raise ValueError("zero has no positive prime factorization")
    runs = [(e, sum(1 for _ in entries)) for e, entries in groupby(reversed(a))]
    lowest = runs[0][0]
    factors = [W(W(g)) for g in lowest]
    previous = lowest
    for i, (exponent, multiplicity) in enumerate(runs):
        if i:
            shared = 0
            while shared < len(previous) and previous[shared] == exponent[shared]:
                shared += 1
            factors.append(succ(W(exponent[shared:])))
        factors.extend(_finite_factors(multiplicity))
        previous = exponent
    return tuple(factors)


def selfcheck():
    f, g = nat(2), nat(3)
    w2, ww = W(f), W(OMEGA)
    terms = [ZERO, ONE, f, g, OMEGA, succ(OMEGA), add(OMEGA, OMEGA),
             w2, add(w2, OMEGA), ww, W(succ(OMEGA)), W(ww)]
    for a, b, c in product(terms, repeat=3):
        assert add(add(a, b), c) == add(a, add(b, c))
        assert mul(mul(a, b), c) == mul(a, mul(b, c))
        assert mul(a, add(b, c)) == add(mul(a, b), mul(a, c))
        assert power(a, add(b, c)) == mul(power(a, b), power(a, c))
        assert power(power(a, b), c) == power(a, mul(b, c))
        if b < c:
            assert add(a, b) < add(a, c)
            assert not a or mul(a, b) < mul(a, c)
            assert a <= ONE or power(a, b) < power(a, c)
            assert power(b, a) <= power(c, a)
    for b in terms:
        q, n = divomega(b)
        assert add(mul(OMEGA, q), nat(n)) == b
        assert power(OMEGA, b) == W(b)
        if b:
            recovered = ONE
            for prime in prime_factors(b):
                assert prime_factors(prime) == (prime,)
                recovered = mul(recovered, prime)
            assert recovered == b
    assert power(f, OMEGA) == OMEGA
    assert power(f, succ(OMEGA)) == add(OMEGA, OMEGA)
    assert power(OMEGA, f) == w2
    print(f"Checked ordinary arithmetic on {len(terms) ** 3} ordered triples.")


if __name__ == "__main__":
    selfcheck()
