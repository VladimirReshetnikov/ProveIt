#!/usr/bin/env python3
"""Independent finite checks of the retained-determinant normalization."""
from __future__ import annotations
from order10_core import (
    A, PRIME, build_factorials, determinant_mod, direct_matrix_order_ten,
    even_bernoulli_mod, retained_matrix_order_ten,
)

p = PRIME
LIMIT = 4 * 14 + 5
fact, invfact = build_factorials(p, LIMIT)
bern = even_bernoulli_mod(30, fact, invfact, p)


def ratio_fact(num: int, den: int) -> int:
    return fact[num] * invfact[den] % p


def h(n: int) -> int:
    return fact[2*n+1]**2 % p * invfact[4*n+2] % p * invfact[4*n+3] % p


def c(n: int) -> int:
    return (2*n+1)*(fact[2*n+2] % p) % p * invfact[4*n+2] % p


def multiplier(a: int, b: int) -> int:
    value = 1
    for t in range(b):
        value = value * ratio_fact(2*b+2*t-2*a+1, 1) % p
    for k in range(b):
        value = value * invfact[2*b-2*k] % p
    for n in range(b-a):
        value = value * h(n) % p
    for i in range(a):
        value = value * c(b-a+i) % p
    eps = a*(b-a)+a*(a-1)//2
    if eps % 2:
        value = -value % p
    return value

for b in range(10, 15):
    direct = determinant_mod(direct_matrix_order_ten(b, bern, fact, invfact, p), p)
    retained = determinant_mod(retained_matrix_order_ten(b, bern, fact, invfact, p), p)
    predicted = multiplier(A,b)*retained % p
    assert direct == predicted, (b,direct,predicted)
    print(f"PASS b={b}: det(M)={direct}, multiplier*det(A)={predicted}")
