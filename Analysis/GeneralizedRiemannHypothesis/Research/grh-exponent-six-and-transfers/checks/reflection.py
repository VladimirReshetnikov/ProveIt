#!/usr/bin/env python3
"""Construct Dickson quintics and certify the local branch and line labels."""
import csv
from collections import Counter
from itertools import combinations
from math import isqrt
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data"


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def quadratic_power(x, y, exponent, d, modulus):
    """(x + y sqrt(d))^exponent as a pair modulo an odd modulus."""
    a, b = 1, 0
    while exponent:
        if exponent % 2:
            a, b = (a*x + d*b*y) % modulus, (a*y + b*x) % modulus
        x, y = (x*x + d*y*y) % modulus, 2*x*y % modulus
        exponent //= 2
    return a, b


def norm_solutions(d):
    for p in range(2, 151):
        if not prime(p) or 4*p >= -d:
            continue
        for b in range(1, 1 + isqrt(4*p**5 // -d)):
            square = 4*p**5 + d*b*b
            a = isqrt(square)
            if a*a == square and a % p and (a-b) % 2 == 0:
                yield p, a, b
                break


def probes(d):
    # Each probe is a homomorphism on the classes represented by the units.
    for s in range(151, 1500, 5):
        if not prime(s):
            continue
        root = next((r for r in range(1, s) if (r*r-d) % s == 0), None)
        if root is None:
            continue
        zeta = next(pow(g, (s-1)//5, s) for g in range(2, s)
                    if pow(g, (s-1)//5, s) != 1)
        yield s, root, zeta


def residue_index(a, b, probe):
    s, root, zeta = probe
    value = (a + b*root) * pow(2, -1, s) % s
    value = pow(value, (s-1)//5, s)
    return [pow(zeta, k, s) for k in range(5)].index(value)


def select_lines(d, h):
    candidates = list(norm_solutions(d))
    if h == 5:
        return [(candidates[0], (), ())]
    assert h == 25
    for probe1, probe2 in combinations(probes(d), 2):
        representatives = {}
        for p, a, b in candidates:
            u, v = (residue_index(a, b, t) for t in (probe1, probe2))
            if u == v == 0:
                continue
            line = (1, v * pow(u, -1, 5) % 5) if u else (0, 1)
            representatives.setdefault(line, ((p, a, b), (probe1, probe2), (u,v)))
        if len(representatives) == 6:
            return sorted(representatives.values())
    raise ArithmeticError(f"Unable to certify six distinct lines over {d}")


def rows():
    with (DATA / "quadratic_inputs.csv").open() as f:
        inputs = list(csv.DictReader(f))
    assert len(inputs) == 27
    for row in inputs:
        d, h = int(row["fundamental_discriminant"]), int(row["class_number"])
        assert prime(-d) and d % 4 == 1 and int(row["class_group_exponent"]) == 5
        fifth = {}
        for x in range(25):
            for y in range(25):
                fifth.setdefault(quadratic_power(x,y,5,d,25), (x,y))
        for (p,a,b), certificates, exponents in select_lines(d,h):
            target = (a*13 % 25, b*13 % 25)  # 1/2 equals 13 modulo 25.
            witness = fifth.get(target)
            v5 = 3 if witness is not None else 5
            yield dict(D=d, class_number=h, p=p, a=a, b=b, v5=v5,
                       field_discriminant=5**v5*d*d,
                       power_basis_index=(5 if v5 == 3 else 1)*b*b,
                       root_x="" if witness is None else witness[0],
                       root_y="" if witness is None else witness[1],
                       probes=" / ".join(",".join(map(str,t)) for t in certificates),
                       residue_indices=",".join(map(str,exponents)))


def main():
    result = list(rows())
    assert len(result) == 37
    with (DATA / "reflected_fields.csv").open("w",newline="") as f:
        writer = csv.DictWriter(f, result[0].keys(), lineterminator="\n")
        writer.writeheader()
        writer.writerows(result)
    for h in (5,25):
        counts = Counter(r["v5"] for r in result if r["class_number"] == h)
        print(f"class number {h}: exponent 3: {counts[3]}, exponent 5: {counts[5]}")
    print("37 projective lines. Norm identities and finite residue tests passed.")


if __name__ == "__main__":
    main()
