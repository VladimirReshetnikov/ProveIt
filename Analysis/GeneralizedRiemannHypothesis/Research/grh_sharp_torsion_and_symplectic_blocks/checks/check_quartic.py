"""Determine the two S4 Frobenius events by exact factor degrees at small primes."""
from collections import Counter
from math import isqrt


def primes(limit):
    return [a for a in range(2, limit+1) if all(a % d for d in range(2, isqrt(a)+1))]


def trim(coeff):
    while coeff and not coeff[-1]:
        coeff.pop()
    return coeff


def remainder(num, den, p):
    coeff = list(num)
    inv = pow(den[-1], -1, p)
    while len(trim(coeff)) >= len(den):
        start = len(coeff)-len(den)
        factor = coeff[-1]*inv
        for i, d in enumerate(den):
            coeff[start+i] = (coeff[start+i]-factor*d) % p
    return coeff


def pow_x_mod_f(power, f, p):
    def multiply(a, b):
        values = [0]*(len(a)+len(b)-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                values[i+j] = (values[i+j]+x*y) % p
        return remainder(values, f, p)
    x, v = [0, 1], [1]
    while power:
        if power % 2:
            v = multiply(v, x)
        x = multiply(x, x)
        power //= 2
    return v


def fixed_roots_in_extension(p, n):
    f = [p-1, p-1, 0, 0, 1]
    coeff = pow_x_mod_f(p**n, f, p)
    coeff = (coeff+[0, 0])[:max(2,len(coeff))]
    coeff[1] = (coeff[1]-1) % p
    b = trim(coeff)
    while b:
        f, b = b, remainder(f, b, p)
    return len(f)-1


def main():
    counts = Counter()
    selected = {8: [], 11: []}
    for p in primes(1000):
        if p == 283:
            continue
        r1 = fixed_roots_in_extension(p, 1)
        r2 = fixed_roots_in_extension(p, 2)
        # For a squarefree quartic, r1 counts its linear factors and r2
        # also counts both roots of each quadratic factor.
        signature = {(4, 4): "1111", (2, 4): "112", (1, 1): "13",
                     (0, 4): "22", (0, 0): "4"}[r1, r2]
        counts[signature] += 1
        if signature == "13":
            selected[8].append(p)
        if signature in ("22", "13"):
            selected[11].append(p)
        if p > 2:
            split_quadratic = pow(-283 % p, (p-1)//2, p) == 1
            assert split_quadratic == (signature in ("1111", "13", "22"))
    print("Factorization types for unramified primes <= 1000:", sorted(counts.items()))
    for support, hits in selected.items():
        print(f"Support {support}/24: {len(hits)} primes; first 10 = {hits[:10]}")


if __name__ == "__main__":
    main()
