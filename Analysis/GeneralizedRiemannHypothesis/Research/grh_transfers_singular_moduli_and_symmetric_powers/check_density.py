"""Exact natural-density bounds for the three prime-adic disk tests."""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import prod


def capped_valuation(value, p, depth):
    count = 0
    while count < depth and value % p == 0:
        count += 1
        value //= p
    return count


def classify(h, p, slope, depth, radius):
    """Classify h mod p^depth for every interval through h of length <= radius."""
    vals = [capped_valuation(h + j, p, depth)
            for j in range(1 - radius, radius)]
    unresolved = depth in vals
    for length in range(1, radius + 1):
        for left in range(length):
            start = radius - 1 - left
            if sum(vals[start:start + length]) >= slope * length:
                return "bad"
    return "split" if unresolved else "good"


def admissible(h, p, sign):
    if p == 2:
        return h % 2 == 0
    return (2 * h + sign) % p != 0


def finite_density(p, slope, radius, sign):
    # Each admissible class has equal mass conditional on the sign mod 4.
    todo = [(h, 1, Fraction(1, p - 1))
            for h in range(p) if admissible(h, p, sign)]
    good = Fraction()
    while todo:
        h, depth, mass = todo.pop()
        status = classify(h, p, slope, depth, radius)
        if status == "good":
            good += mass
        elif status == "split":
            assert depth < slope * radius
            modulus = p**depth
            todo.extend((h + a * modulus, depth + 1, mass / p)
                        for a in range(p))
    return good


def tail_bound(p, slope, radius):
    a = radius + 1
    step = p - 1
    power = slope * step - 1

    def term(r):
        exponent = (power * r + step - 1) // step
        return Fraction(2 * r - 1, (p - 1) * p**(exponent - 1))

    ratio = Fraction(2 * (a + step) - 1, (2 * a - 1) * p**power)
    return sum(term(r) for r in range(a, a + step)) / (1 - ratio)


def decimal(q):
    with localcontext() as ctx:
        ctx.prec = 28
        return Decimal(q.numerator) / Decimal(q.denominator)


def direct_small_test(p, slope, radius):
    """Enumerate all shallow classes independently of the recursive pruning."""
    modulus = p**(slope * radius)
    for sign in (-1, 1):
        accepted = 0
        for h in range(modulus):
            if not admissible(h, p, sign):
                continue
            good = True
            for left in range(1-radius, 1):
                for right in range(0, radius + left):
                    product = 1
                    for j in range(left, right+1):
                        product *= h + j
                    if product % p**(slope * (right-left+1)) == 0:
                        good = False
            accepted += good
        assert Fraction(accepted, modulus - modulus // p) == finite_density(
            p, slope, radius, sign)


if __name__ == "__main__":
    direct_small_test(2, 4, 2)
    direct_small_test(7, 2, 2)
    direct_small_test(3, 3, 2)
    lower = []
    upper = []
    for p, slope, radius in [(2, 4, 25), (3, 3, 16), (7, 2, 10)]:
        d = finite_density(p, slope, radius, 1)
        assert d == finite_density(p, slope, radius, -1)
        error = tail_bound(p, slope, radius)
        print(f"p={p}, depth={slope}, radius={radius}")
        print("  finite density", d, decimal(d))
        print("  tail upper bound", error, decimal(error))
        print("  infinite lower bound", decimal(d - error))
        lower.append(d-error)
        upper.append(d)
    lower_union = 1 - prod(1-d for d in lower)
    upper_union = 1 - prod(1-d for d in upper)
    print("three-prime union lower bound", decimal(lower_union))
    print("three-prime union upper bound", decimal(upper_union))
