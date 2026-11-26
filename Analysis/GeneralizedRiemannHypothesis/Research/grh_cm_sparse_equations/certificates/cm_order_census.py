#!/usr/bin/env python3
"""All imaginary quadratic order discriminants of class numbers four and five.

Watkins, Class numbers of imaginary quadratic fields, Table 4 supplies the
unconditional bounds on fundamental discriminants used in FIELD_MAXIMUM.
The output counts primitive reduced positive binary quadratic forms.
"""
from math import gcd, isqrt
from collections import Counter

FIELD_MAXIMUM = {1: 163, 2: 427, 4: 1555, 5: 2683}

def prime_powers(n):
    prime = 2
    while prime*prime <= n:
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if exponent:
            yield prime, exponent
        prime += 1
    if n > 1:
        yield n, 1

def squarefree(n):
    return all(e == 1 for _, e in prime_powers(n))

def fundamental(d):
    return ((d % 4 == 1 and squarefree(-d)) or
            (d % 4 == 0 and d//4 % 4 in (2, 3) and squarefree(-d//4)))

def reduced_form_count(d):
    count = 0
    for a in range(1, isqrt(-d//3)+1):
        for b in range(-a, a+1):
            c, rem = divmod(b*b-d, 4*a)
            if rem == 0 and a <= c and gcd(gcd(a,b),c) == 1:
                if b >= 0 or (-b < a < c):
                    count += 1
    return count

def quadratic_symbol(d,p):
    if d % p == 0:
        return 0
    if p == 2:
        return 1 if d % 8 in (1,7) else -1
    return 1 if pow(d % p,(p-1)//2,p) == 1 else -1

def order_class_number(d,h,f):
    if f == 1:
        return h
    value = h
    for p,e in prime_powers(f):
        value *= p**(e-1)*(p-quadratic_symbol(d,p))
    index = {-3:3,-4:2}.get(d,1)
    assert value % index == 0
    return value//index

def census():
    orders = {4:[], 5:[]}
    fields = Counter()
    for D in range(3, max(FIELD_MAXIMUM.values())+1):
        d = -D
        if not fundamental(d):
            continue
        h = reduced_form_count(d)
        if h not in FIELD_MAXIMUM:
            continue
        assert D <= FIELD_MAXIMUM[h]
        fields[h] += 1
        for target in orders:
            if target % h:
                continue
            # phi(f) <= 3*target/h and phi(f)^2 >= f/2.
            f_bound = 2*(3*target//h)**2
            for f in range(1,f_bound+1):
                if order_class_number(d,h,f) == target:
                    orders[target].append(D*f*f)
    assert fields == {1:9,2:18,4:54,5:25}
    return {h:sorted(ds) for h,ds in orders.items()}

if __name__ == '__main__':
    for h, discriminants in census().items():
        print(f'h = {h}, {len(discriminants)} orders, absolute discriminants')
        print(', '.join(map(str, discriminants)))
