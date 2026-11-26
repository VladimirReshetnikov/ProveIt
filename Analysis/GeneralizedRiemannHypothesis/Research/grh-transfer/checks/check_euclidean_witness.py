#!/usr/bin/env python3
"""Exact check of one non-norm-Euclidean cyclic field from Lezowski–McGown.

Reference: arXiv:1601.03433v2, Table 3.1 first row and Proposition 3.1.
Only the finite arithmetic premises of that proposition are checked here.
"""
from math import gcd, isqrt

degree = 97
conductor = 59_999_999_974_303
q1, q2, r = 2, 3, 431

def prime(n):
    if n < 2 or n % 2 == 0:
        return n == 2
    return all(n % divisor != 0 for divisor in range(3, isqrt(n) + 1, 2))

def verify(label, condition):
    if not condition:
        raise ValueError(label)
    print("PASS", label)

verify("Prime conductor f", prime(conductor))
verify("97 divides f-1", (conductor - 1) % degree == 0)
# F_f^* is cyclic. The displayed homomorphism has kernel of index 97,
# the splitting subgroup for the unique degree-97 field of conductor f.
def character(n):
    return pow(n, (conductor - 1) // degree, conductor)

verify("2 and 3 are inert, hence are the first two inert primes",
       all(character(q) != 1 for q in (q1, q2)))
verify("r coprime to 6 and chi(r)*chi(3)=1",
       gcd(r, q1 * q2) == 1 and character(r * q2) == 1)
verify("3*r*k differs from f modulo 4 for 1 <= k < 2",
       all((r * q2 * k - conductor) % (q1 * q1) != 0 for k in range(1, q1)))
verify("(q1-1)*(q2*r-1) <= f", (q1 - 1) * (q2 * r - 1) <= conductor)
print("Proposition 3.1 excludes this field from the norm-Euclidean list.")
