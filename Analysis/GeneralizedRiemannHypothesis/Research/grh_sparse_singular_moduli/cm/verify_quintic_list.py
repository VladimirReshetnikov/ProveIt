#!/usr/bin/env python3
"""Class-number-five order census from Watkins's fundamental-discriminant bound."""
import json
from math import isqrt
from pathlib import Path
from verify_class_polynomials import reduced_forms

HERE = Path(__file__).resolve().parent


def prime_divisors(n):
    primes = []
    q = 2
    while q*q <= n:
        if n % q == 0:
            primes.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        primes.append(n)
    return primes


def is_squarefree(n):
    return all(n % (p*p) for p in prime_divisors(n))


def is_fundamental(D):
    if D % 4 == 1:
        return is_squarefree(-D)
    return D % 4 == 0 and (D//4) % 4 in (2, 3) and is_squarefree(-D//4)


def kronecker_at_prime(D, p):
    if D % p == 0:
        return 0
    if p == 2:
        return 1 if D % 8 in (1, 7) else -1
    return 1 if pow(D, (p-1)//2, p)==1 else -1


def main():
    # Watkins gives maximum |D_K| 163 and 2683 for h_K=1 and 5, respectively.
    fields = {1: [], 5: []}
    for absD in range(3, 2684):
        if is_fundamental(-absD):
            h = sum(1 for _ in reduced_forms(absD))
            if h in fields:
                fields[h].append(-absD)
    assert len(fields[1])==9 and len(fields[5])==25
    # phi(f) <= 15 for all possible conductors, and phi(f)^2 >= f/2.
    orders = set()
    for h, ds in fields.items():
        for D in ds:
            for f in range(1, 451):
                m = f
                for p in prime_divisors(f):
                    m = m//p*(p-kronecker_at_prime(D,p))
                units = 1 if f==1 else {-3: 3, -4: 2}.get(D,1)
                if h*m == 5*units:
                    orders.add(D*f*f)
    coeffs = json.loads((HERE/"class_polynomials.json").read_text())
    assert orders == {int(D) for D, c in coeffs.items() if len(c) == 6}
    assert len(orders)==29
    print("All 29 class-number-five order discriminants match the degree-five polynomial list.")


if __name__ == "__main__":
    main()
