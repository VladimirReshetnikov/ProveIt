"""Construct the weight-two CM quintic field list and certify its distinctness.

Polynomial arithmetic uses ascending coefficients. At a prime where the reduction
is squarefree, its factor degrees give the residue degrees in the number field.
"""
from csv import writer
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
import sys


def primes_up_to(bound):
    return [p for p in range(2, bound + 1)
            if all(p % n for n in range(2, isqrt(p) + 1))]


def class_number(D):
    """Count reduced primitive positive definite forms of discriminant D."""
    count = 0
    for a in range(1, isqrt(abs(D) // 3) + 1):
        for b in range(-a, a + 1):
            c, rem = divmod(b*b - D, 4*a)
            if rem or a > c or (b < 0 and (abs(b) == a or a == c)):
                continue
            if gcd(a, gcd(b, c)) == 1:
                count += 1
    return count


def fundamental(D):
    # Negative fundamental discriminants are squarefree = 1 mod 4 or
    # four times squarefree m with m = 2 or 3 mod 4.
    if D % 4 == 1:
        m = D
    elif D % 4 == 0 and (D // 4) % 4 in (2, 3):
        m = D // 4
    else:
        return False
    return all(m % (k*k) for k in range(2, isqrt(abs(m)) + 1))


def represents_prime(q, p):
    for b in range(isqrt(4*p//q) + 1):
        value = 4*p - q*b*b
        a = isqrt(value)
        if a*a == value and (a-b) % 2 == 0:
            return True
    return False


def field_parameters(q):
    # For D=-q the norm of (a+b sqrt(-q))/2 is (a^2+q b^2)/4.
    # All fields in this finite class-number-five list have odd prime q=3 mod 4.
    for p in primes_up_to(200):
        if p == q:
            continue
        if represents_prime(q, p):
            continue
        for b in range(1, isqrt(4*p**5//q)+1):
            val = 4*p**5-q*b*b
            a = isqrt(val)
            if a*a == val and (a-b) % 2 == 0 and a % p:
                return p, a, b
    raise ValueError(f"No suitable split prime found for discriminant {-q}")


def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def remainder(f, g, ell):
    f = trim([x % ell for x in f])
    inverse = pow(g[-1], -1, ell)
    while len(f) >= len(g):
        shift = len(f)-len(g)
        multiplier = f[-1]*inverse % ell
        for j, b in enumerate(g):
            f[j+shift] = (f[j+shift]-multiplier*b) % ell
        trim(f)
    return f


def poly_gcd(f, g, ell):
    while g:
        f, g = g, remainder(f, g, ell)
    return f


def mul_mod(f, g, mod, ell):
    prod = [0] * (len(f)+len(g))
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            prod[i+j] += a*b
    return remainder(prod, mod, ell)


def power_mod(f, n, mod, ell):
    ans = [1]
    while n:
        if n % 2:
            ans = mul_mod(ans, f, mod, ell)
        f = mul_mod(f, f, mod, ell)
        n //= 2
    return ans


def splitting(f, ell):
    derivative = trim([(i*f[i]) % ell for i in range(1, len(f))])
    if len(poly_gcd(f, derivative, ell)) > 1:
        return None
    x_power = [0, 1]
    degrees = []
    for d in range(1, 6):
        x_power = power_mod(x_power, ell, f, ell)
        diff = (x_power + [0, 0])[:max(2,len(x_power))]
        diff[1] = (diff[1]-1) % ell
        total = len(poly_gcd(f, trim(diff), ell))-1
        new = total - sum(j for j in degrees if d % j == 0)
        assert new >= 0 and new % d == 0
        degrees.extend([d]*(new//d))
        if sum(degrees) == 5:
            return tuple(degrees)
    raise ArithmeticError("Invalid splitting pattern")


def main():
    fields = [("cyclotomic", [1,3,-3,-4,1,1])]
    out = writer(sys.stdout, lineterminator="\n")
    out.writerow(["D_E","p","a","b","coefficient_x3","coefficient_x","constant"])
    ds = [D for D in range(-3, -2684, -1) if fundamental(D) and class_number(D)==5]
    assert len(ds)==25 and ds[-1]==-2683
    for D in ds:
        q = -D
        assert q % 4 == 3 and q in primes_up_to(2683)
        p,a,b = field_parameters(q)
        f = [-a,5*p*p,0,-5*p,0,1]
        fields.append((str(D),f))
        out.writerow([D,p,a,b,f[3],f[1],f[0]])
    witnesses = {}
    irreducible = {}
    for ell in primes_up_to(1000):
        types = {name:splitting(f,ell) for name,f in fields}
        for name,kind in types.items():
            if kind==(5,):
                irreducible.setdefault(name,ell)
        for u,v in combinations(types,2):
            a,b = types[u],types[v]
            if a and b and a!=b:
                witnesses.setdefault((u,v),(ell,a,b))
        if len(irreducible)==26 and len(witnesses)==325:
            break
    assert len(irreducible)==26 and len(witnesses)==325
    dest = Path(__file__).resolve().parent
    with (dest/"quintic_witnesses.csv").open("w",newline="") as fp:
        out = writer(fp,lineterminator="\n")
        out.writerow(["field1","field2","prime","factor_degrees1","factor_degrees2"])
        for pair,(ell,a,b) in witnesses.items():
            out.writerow([*pair,ell,"+".join(map(str,a)),"+".join(map(str,b))])
    with (dest/"quintic_irreducible.csv").open("w",newline="") as fp:
        out = writer(fp,lineterminator="\n")
        out.writerow(["field","irreducible_mod_prime"])
        out.writerows(irreducible.items())


if __name__ == "__main__":
    main()
