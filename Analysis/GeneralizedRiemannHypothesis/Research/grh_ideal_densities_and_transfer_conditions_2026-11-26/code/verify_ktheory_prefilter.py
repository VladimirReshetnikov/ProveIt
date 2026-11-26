#!/usr/bin/env python3
"""Exact preparatory computations for the K-theory transfer, using Python only.

This proves finite rational identities and representation dimensions. It does NOT
prove a K-group vanishes or verify the original Selmer/automorphy interface.

Run: python3 verify_ktheory_prefilter.py --output prefilter_results.json
Use --ranks to additionally count the compact invariant-space dimensions.

Definitions: b_d(n)=B_{n+1,chi_-d}/(n+1), d=3 or 7; the character is the
Legendre character modulo d. A_d(e)=|num b_d(e) * num b_d(2e)|.
The exponential-series recurrence and the Bernoulli-polynomial formula are
implemented independently and compared exactly for every displayed value.
"""

import argparse
from fractions import Fraction as Q
from math import comb, gcd
import json
from pathlib import Path


def character(d, a):
    a %= d
    if not a:
        return 0
    return 1 if pow(a, (d - 1) // 2, d) == 1 else -1


def via_exponentials(d, bound):
    # sum b_d(n)t^n/n! = sum chi(a)exp(a*t)/(exp(d*t)-1).
    answer = []
    for n in range(bound + 1):
        numerator = sum(character(d, a) * a ** (n + 1) for a in range(1, d))
        known = sum(Q(comb(n + 1, j) * d**j) * answer[n + 1 - j]
                    for j in range(2, n + 2))
        answer.append((Q(numerator) - known) / ((n + 1) * d))
    return answer


def ordinary_bernoulli(bound):
    # The defining relation sum binom(n+1,j) B_j=0, n>=1; B_1=-1/2.
    table = [Q(1)]
    for n in range(1, bound + 1):
        table.append(-sum(Q(comb(n + 1, j)) * table[j]
                          for j in range(n)) / (n + 1))
    return table


def via_bernoulli_polynomial(d, n, bernoulli):
    # B_m,chi = d^(m-1) sum_a chi(a) B_m(a/d), with m=n+1.
    m = n + 1
    total = Q(0)
    for a in range(1, d):
        polynomial = sum(Q(comb(m, j)) * bernoulli[j] * Q(a, d)**(m - j)
                         for j in range(m + 1))
        total += character(d, a) * polynomial
    return d**(m - 1) * total / m


def small_factorization(n):
    """Only for the small positive gcds and denominators, not huge numerators."""
    assert n > 0
    result = {}
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            result[str(p)] = exponent
        p += 1
    if n > 1:
        result[str(n)] = result.get(str(n), 0) + 1
    return result


def bezout(a, b):
    """Return an explicit integer certificate x*a+y*b=gcd(a,b)."""
    r0,r1=a,b
    x0,x1,y0,y1=1,0,0,1
    while r1:
        q,r=divmod(r0,r1)
        r0,r1=r1,r
        x0,x1=x1,x0-q*x1
        y0,y1=y1,y0-q*y1
    assert x0*a+y0*b==r0==gcd(a,b)
    return {"x":str(x0),"y":str(y0),"gcd":str(r0)}


def invariant_orbits(n, roots):
    # Monomials x^a y^b invariant under mu_roots^3 satisfy a_i=b_i mod roots.
    # S_3 invariants have the orbit-sum basis encoded by sorted coordinate pairs.
    if n < 0:
        return set()
    result = set()
    for a0 in range(n + 1):
        for a1 in range(n + 1 - a0):
            a = (a0, a1, n - a0 - a1)
            r = tuple(v % roots for v in a)
            k = (n - sum(r)) // roots
            for b0 in range(k + 1):
                for b1 in range(k + 1 - b0):
                    b = (r[0] + roots*b0, r[1] + roots*b1,
                         r[2] + roots*(k - b0 - b1))
                    result.add(tuple(sorted(zip(a, b))))
    return result


def compact_ranks(e, roots):
    # Quotient by x.y: equivariant multiplication by x.y is injective, and
    # finite-group invariants are exact in characteristic zero. Swapping x,y acts by permutation
    # on orbit sums. Hence subtract orbit dimensions and fixed-orbit counts.
    current, previous = invariant_orbits(e-1, roots), invariant_orbits(e-2, roots)
    fixed = lambda collection: sum(tuple(sorted((b, a) for a, b in orbit)) == orbit
                                   for orbit in collection)
    dimension = len(current) - len(previous)
    trace = fixed(current) - fixed(previous)
    assert (dimension - trace) % 2 == 0
    return {"e": e, "K_degree": 2*e, "roots_of_unity": roots,
            "full_dimension": dimension, "swap_trace": trace,
            "negative_dimension": (dimension-trace)//2}


def run(include_ranks=False):
    last = 80
    tables = {d: via_exponentials(d, 2*last) for d in (3, 7)}
    bernoulli = ordinary_bernoulli(2*last+1)
    rows = []
    for e in range(54, last+1, 2):
        fields = {}
        for d in (3, 7):
            fractions = {}
            for n in (0, e, 2*e):
                value = tables[d][n]
                assert value == via_bernoulli_polynomial(d, n, bernoulli)
                fractions[str(n)] = {"numerator": str(value.numerator),
                                      "denominator": value.denominator,
                                      "denominator_factors": small_factorization(value.denominator)}
            product = abs(tables[d][e].numerator * tables[d][2*e].numerator)
            fields[str(d)] = {"b_values": fractions, "A": str(product),
                              "A_digits": len(str(product))}
        common = gcd(int(fields["3"]["A"]), int(fields["7"]["A"]))
        factorization = small_factorization(common)
        rows.append({"e": e, "K_degree": 2*e, "fields": fields,
                     "gcd_A3_A7": str(common), "gcd_factors": factorization,
                     "bezout_certificate":bezout(int(fields["3"]["A"]),int(fields["7"]["A"]))})
    assert next(r for r in rows if r["e"] == 62)["gcd_A3_A7"] == "4"
    assert next(r for r in rows if r["e"] == 64)["gcd_A3_A7"] == "4"
    assert all(all(int(p) <= 109 for p in r["gcd_factors"]) for r in rows)
    assert all(all(int(p) in (3, 7) for p in data["denominator_factors"])
               for row in rows for field in row["fields"].values()
               for data in field["b_values"].values())
    answer = {"status": "Exact preparatory identities; no K-group vanishing established",
              "methods": ["exponential-series recurrence", "Bernoulli-polynomial formula"],
              "rows": rows}
    if include_ranks:
        ranks = [compact_ranks(e, roots) for e in (52, 60, 62, 64) for roots in (6, 4)]
        assert next(r for r in ranks if r["e"] == 52 and r["roots_of_unity"] == 6)["negative_dimension"] == 324
        assert next(r for r in ranks if r["e"] == 60 and r["roots_of_unity"] == 4)["negative_dimension"] == 1120
        answer["compact_ranks"] = ranks
    return answer


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--ranks", action="store_true")
    args = parser.parse_args()
    result = run(args.ranks)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    for row in result["rows"]:
        print(f"e={row['e']:2} degree={row['K_degree']:3} gcd(A3,A7)={row['gcd_A3_A7']}")
    for rank in result.get("compact_ranks", []):
        print("compact rank", rank)
    print("PASS: all displayed rational values agree under two independent exact formulas.")
