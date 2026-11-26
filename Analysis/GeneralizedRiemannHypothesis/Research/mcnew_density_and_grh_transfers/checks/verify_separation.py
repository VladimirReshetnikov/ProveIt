"""Verify the finite lemma and the global numerical lower bound for McNew 7.4."""
from fractions import Fraction as F
from math import isqrt, lcm
from pathlib import Path
from finite_weights import reciprocal_sum, smooth_through, verify_threshold

N = 10**6
Y = 10**5
tau = F(83, 1000)
gain = F(23, 10000)
values = smooth_through((2, 3, 5), N)
replacement = set(map(int, Path(__file__).with_name("replacement.txt").read_text().split()))
assert len(replacement) == 102 and replacement <= set(values) and len(values) == 507
for a in replacement:
    for ratio in range(2, isqrt(N // a) + 1):
        assert a * ratio not in replacement or a * ratio**2 not in replacement

# sum_{n>100} 1/n^2 <= 1/100 by integration.
assert sum(F(1, n*n) for n in range(1, 101)) + F(1, 100) - F(25, 16) < tau
tail = F(15, 4) - reciprocal_sum(values)
scale = lcm(*values) * tau.denominator
coefficients = [scale * ((1 - tau) if n in replacement else F(1)) / n for n in values]
assert all(coefficient.denominator == 1 for coefficient in coefficients)
threshold = scale * ((1 - tau) * reciprocal_sum(replacement) - tail - gain)
nodes = verify_threshold(values, list(map(int, coefficients)), threshold.__floor__())
print("smooth integers", len(values), "replacement size", len(replacement))
print("replacement weight", reciprocal_sum(replacement), "tail weight", tail)
print("weight scale", scale, "integer threshold", threshold.__floor__(), "search nodes", nodes)
print("uniform unnormalized gain >=", gain)

sieve = bytearray([1]) * (Y + 1)
sieve[:2] = bytes(2)
for p in range(2, isqrt(Y) + 1):
    if sieve[p]:
        sieve[p*p::p] = bytes((Y-p*p)//p + 1)
precision = 10**18
product_floor = precision
for prime in range(2, Y + 1):
    if sieve[prime]:
        product_floor = product_floor * (prime - 1) // prime
lower = F(product_floor, precision) * gain - F(1, Y)
assert lower > F(1, 10000)
print("c_Y lower bound", F(product_floor, precision), "Y", Y)
print("beta-alpha >=", lower, "> 1/10000")
