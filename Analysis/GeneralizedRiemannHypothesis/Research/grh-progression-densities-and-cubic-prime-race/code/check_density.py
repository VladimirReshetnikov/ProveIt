"""Rational certificates for the joint valuation exchange and the fiber example."""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def is_ap_free(values):
    values = set(values)
    return all(2*b-a not in values for a, b in combinations(sorted(values), 2))


def allowed(exponent):
    while exponent:
        exponent, digit = divmod(exponent, 3)
        if digit == 2:
            return False
    return True


def density_certificate(q, degrees):
    weights = [Fraction(1, q**degree) for degree in degrees]
    new_mass = prod(1+w for w in weights) - 1
    # A positive exponent below 9 can only be 1, 3, or 4.
    old_upper = prod(1+w*w+w**3+w**8/(1-w) for w in weights)
    surplus = new_mass-old_upper
    unconditional_gain = (1-Fraction(1, q))*prod(w*(1-w) for w in weights)*surplus
    return surplus, unconditional_gain


def check_exchange_dimension(k, limit):
    """Direct check on a truncated grid, separate from the unbounded proof."""
    def keep(point):
        if min(point) == 0:
            return all(map(allowed, point))
        return max(point) == 2 and all(x in (1, 2) for x in point)

    count = 0
    for start in product(range(limit+1), repeat=k):
        if not keep(start):
            continue
        for step in product(*(range((limit-x)//2+1) for x in start)):
            if not any(step):
                continue
            middle = tuple(x+h for x, h in zip(start, step))
            end = tuple(x+2*h for x, h in zip(start, step))
            assert not (keep(middle) and keep(end))
            count += 1
    return count


if __name__ == '__main__':
    for q, degrees, minimum in [(2,[1,1,2,3],'0.00004244'),
                                (3,[1,1,1,2],'0.00007119'),
                                (4,[1,1,1,1],'0.00008364')]:
        bracket, gain = density_certificate(q, degrees)
        assert gain > Fraction(minimum)
        print(f'q={q}: bracket >= {bracket}; density gain >= {gain} > {minimum}')
    A8 = [a for a in range(9) if allowed(a)]
    witness = [0,1,3,7,8]
    assert len(A8) == 4 and len(witness) == 5 and is_ap_free(witness)
    print(f'Greedy exponents at cutoff 8: {A8}; replacement: {witness}')
    for k in (2,3,4):
        print(f'Checked {check_exchange_dimension(k, 8)} candidate triples in [0,8]^{k}.')
