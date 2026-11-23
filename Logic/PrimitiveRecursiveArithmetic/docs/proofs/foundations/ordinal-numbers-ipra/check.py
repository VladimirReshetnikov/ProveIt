"""Independent finite regressions for the manuscript. Python 3, standard library.

Run without arguments. The mathematical proofs cover all valid inputs.
"""
from itertools import groupby, product
from collections import Counter
from arithmetic import ZERO, ONE, OMEGA, W, nat, add, mul, succ, selfcheck


def residual(left, result):
    if result < left:
        raise ValueError("left residual is defined for left <= result")
    i = 0
    while i < len(left) and i < len(result) and left[i] == result[i]:
        i += 1
    return result[i:]


def divide(dividend, divisor):
    """Return quotient, remainder for dividend = divisor*quotient + remainder."""
    if not divisor:
        raise ValueError("zero divisor")
    degree = divisor[0]
    cut = 0
    while cut < len(dividend) and dividend[cut] > degree:
        cut += 1
    large = tuple(residual(degree, exponent) for exponent in dividend[:cut])
    tail = dividend[cut:]
    bound = tail.count(degree)
    j = max(k for k in range(bound + 1) if mul(divisor, nat(k)) <= tail)
    return large + nat(j), residual(mul(divisor, nat(j)), tail)


def natural_sum(a, b):
    return tuple(sorted(a + b, reverse=True))


def natural_product(a, b):
    return tuple(sorted((natural_sum(e, f) for e in a for f in b), reverse=True))


def fundamental(lam, n):
    if not lam or not lam[-1]:
        return ZERO
    e = lam[-1]
    if e[-1] == ZERO:
        return lam[:-1] + (e[:-1],) * (n + 1)
    return lam[:-1] + (fundamental(e, n),)


def maximum_run(a):
    local = max((sum(1 for _ in group) for _, group in groupby(a)), default=0)
    return max([local] + [maximum_run(e) for e in a])


def first_index(lam, y):
    """Least n with y < F(lam,n), for a positive limit lam > y."""
    if not lam or not lam[-1] or y >= lam:
        raise ValueError("expected a positive limit strictly above the comparator")
    prefix = lam[:-1]
    if len(y) <= len(prefix) or y[:len(prefix)] != prefix:
        return 0
    e, d = lam[-1], y[len(prefix)]
    if e[-1]:
        return first_index(e, d)
    if d != e[:-1]:
        return 0
    return sum(1 for _ in next(groupby(y[len(prefix):]))[1])


def nodes(a):
    return 1 + sum(nodes(e) for e in a)


def terms_up_to(size):
    """Construct canonical rooted trees by exact node count and decreasing entries."""
    groups = {1: [ZERO]}
    for count in range(2, size + 1):
        def children(remaining, upper):
            if remaining == 0:
                yield ()
                return
            for w in range(1, remaining + 1):
                for e in groups.get(w, ()):
                    if upper is None or e <= upper:
                        for tail in children(remaining - w, e):
                            yield (e,) + tail
        groups[count] = list(children(count - 1, None))
    return [a for k in range(1, size + 1) for a in groups[k]]


def hereditary(n, base):
    ascending = []
    e = 0
    while n:
        n, digit = divmod(n, base)
        if digit:
            ascending.extend([hereditary(e, base)] * digit)
        e += 1
    return tuple(reversed(ascending))


def evaluate(word, base):
    return sum(base ** evaluate(e, base) for e in word)


def mex(values):
    x = 0
    while x in values:
        x += 1
    return x


def main():
    selfcheck()
    terms = terms_up_to(7)
    assert len(terms) == len(set(terms))
    assert Counter(map(nodes, terms)) == {1: 1, 2: 1, 3: 2, 4: 4, 5: 9, 6: 20, 7: 48}
    ndiv = ncof = 0
    for a, b in product(terms, repeat=2):
        if a <= b:
            assert add(a, residual(a, b)) == b
        if a:
            q, r = divide(b, a)
            assert r < a and add(mul(a, q), r) == b < mul(a, succ(q))
            ndiv += 1
        if a and a[-1] and b < a:
            n = nodes(b)
            assert b < fundamental(a, n) < fundamental(a, n + 1) < a
            m = first_index(a, b)
            assert m <= maximum_run(b) and b < fundamental(a, m)
            assert m == 0 or fundamental(a, m - 1) <= b
            ncof += 1
        assert add(a, b) <= natural_sum(a, b)
        assert mul(a, b) <= natural_product(a, b)
    small = terms_up_to(5)
    for a, b, c in product(small, repeat=3):
        assert natural_sum(natural_sum(a, b), c) == natural_sum(a, natural_sum(b, c))
        assert natural_product(natural_product(a, b), c) == natural_product(a, natural_product(b, c))
        assert natural_product(a, natural_sum(b, c)) == natural_sum(natural_product(a, b), natural_product(a, c))
        if b < c:
            assert natural_sum(a, b) < natural_sum(a, c)
            assert not a or natural_product(a, b) < natural_product(a, c)
    for a, b in product(range(36), repeat=2):
        options = {i ^ b for i in range(a)} | {a ^ j for j in range(b)}
        assert mex(options) == (a ^ b)
    for b in range(2, 8):
        for n in range(1, 130):
            word = hereditary(n, b)
            assert evaluate(word, b) == n
            m = evaluate(word, b + 1)
            assert hereditary(m, b + 1) == word
            assert hereditary(m - 1, b + 1) < word
    print(f"Checked {len(terms)} canonical trees, {ndiv} divisions, {ncof} cofinality witnesses.")
    print(f"Checked {len(small)**3} natural-operation triples, 1296 finite mex equations, 774 base changes.")
    from epsilon import selfcheck as epsilon_check
    epsilon_check()
    from digits import selfcheck as digits_check
    digits_check()


if __name__ == "__main__":
    main()
