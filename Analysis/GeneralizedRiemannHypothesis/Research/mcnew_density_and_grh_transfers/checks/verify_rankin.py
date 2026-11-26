"""Check the low digit boxes and a rational bound for the infinite tail."""
from fractions import Fraction as F
from itertools import product
from math import prod
from finite_weights import verify_threshold


def allowed(exponent):
    while exponent:
        if exponent % 3 == 2:
            return False
        exponent //= 3
    return True


def check(primes, digits, multiplier):
    limits = [3**k for k in digits]
    grid = product(*(range(limit) for limit in limits))
    points = sorted((prod(p**e for p, e in zip(primes, exponents)),
                     all(map(allowed, exponents))) for exponents in grid)
    values = [v for v, _ in points]
    common = max(values) * multiplier.denominator
    weights = [F(common, v) * (1 if good else multiplier) for v, good in points]
    assert all(w.denominator == 1 for w in weights)
    target = sum(int(w) for w, (_, good) in zip(weights, points) if good)
    nodes = verify_threshold(values, list(map(int, weights)), target)
    charge = F()
    for step in (1, 2):
        low = prod(1 + F(1, p**(step * 3**j)) for p,k in zip(primes,digits) for j in range(k))
        # Finite-subset powers of 3 are distinct, and form a subset of all powers.
        high = prod(1 / (1-F(1, p**(step * limit))) for p,limit in zip(primes,limits))
        charge += low * (high - 1)
    margin = 1 - 1 / multiplier - charge
    assert margin > 0
    print("primes", primes, "digit depths", digits, "box size", len(values), "multiplier", multiplier)
    print("search nodes",nodes,"certified stability margin", margin)


for instance in [((2,3),(2,2),F(51,50)),((2,3,5),(2,2,1),F(11,10)),
                 ((2,3,5,7),(2,2,1,1),F(21,20))]:
    check(*instance)

for primes in [(2,3), (2,3,5), (2,3,5,7)]:
    partial = prod(F(p-1,p) for p in primes)
    for p in primes:
        for j in range(4):
            partial *= 1 + F(1, p**(3**j))
    upper = partial * prod(1/(1-F(1, p**81)) for p in primes)
    print("density interval, multiplied by 10^9", primes,
          (partial*10**9).__floor__(), (upper*10**9).__ceil__())
