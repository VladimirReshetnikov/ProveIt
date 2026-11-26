#!/usr/bin/env python3
"""Independently check every quintic factorization witness with SymPy."""
import csv
from itertools import combinations
from pathlib import Path

import sympy as sp


def rows(filename):
    with Path(__file__).with_name(filename).open(newline="") as stream:
        return list(csv.DictReader(stream))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def polynomial_fields():
    x, z = sp.symbols("x z")
    elimination = sp.resultant(sp.cyclotomic_poly(11, z), z**2 - x*z + 1, z)
    coeff, factors = sp.factor_list(elimination)
    require(coeff == 1 and len(factors) == 1 and factors[0][1] == 2,
            "Unexpected real cyclotomic resultant")
    fields = {"cyclotomic": sp.Poly(factors[0][0], x)}
    for row in rows("quintic_fields.csv"):
        disc, prime, trace, imag = (int(row[key]) for key in ("D_E", "p", "a", "b"))
        require(sp.isprime(-disc) and sp.isprime(prime), row)
        require(trace**2 - disc*imag**2 == 4*prime**5 and prime != -disc, row)
        polynomial = x**5 + int(row["coefficient_x3"])*x**3 + int(row["coefficient_x"])*x + int(row["constant"])
        require(sp.expand(polynomial - (x**5 - 5*prime*x**3 + 5*prime**2*x - trace)) == 0, row)
        require(str(disc) not in fields, f"Duplicate CM discriminant {disc}")
        fields[str(disc)] = sp.Poly(polynomial, x)
    require(len(fields) == 26, "Incorrect number of field polynomials")
    return fields


def main():
    fields = polynomial_fields()
    table = rows("quintic_polynomials.csv")
    require(len(table) == len(fields) and {row["field"] for row in table} == set(fields),
            "The full polynomial table has missing or repeated rows")
    for row in table:
        name = row["field"]
        coefficients = [int(row[f"x{degree}"]) for degree in range(5, -1, -1)]
        require(coefficients == fields[name].all_coeffs(), f"Incorrect polynomial for {name}")
        require(row["cm_discriminant"] == ("-11" if name == "cyclotomic" else name),
                f"Incorrect CM discriminant for {name}")
    cache = {}

    def factor_degrees(name, prime):
        key = (name, prime)
        if key not in cache:
            require(sp.isprime(prime), f"Nonprime witness {prime}")
            polynomial = fields[name].set_modulus(prime)
            coeff, factors = polynomial.factor_list()
            require(coeff == 1 and all(m == 1 for _, m in factors), f"Ramified witness {key}")
            degrees = sorted(f.degree() for f, _ in factors)
            require(sum(degrees) == 5, key)
            cache[key] = "+".join(map(str, degrees))
        return cache[key]

    irreducibles = rows("quintic_irreducible.csv")
    require(len(irreducibles) == 26 and {r["field"] for r in irreducibles} == set(fields),
            "Missing irreducibility check")
    for row in irreducibles:
        require(factor_degrees(row["field"], int(row["irreducible_mod_prime"])) == "5", row)

    witnesses = rows("quintic_witnesses.csv")
    pairs = set()
    for row in witnesses:
        a, b, prime = row["field1"], row["field2"], int(row["prime"])
        ta, tb = factor_degrees(a, prime), factor_degrees(b, prime)
        require(ta == row["factor_degrees1"] and tb == row["factor_degrees2"] and ta != tb, row)
        pairs.add(frozenset((a, b)))
    expected = {frozenset(pair) for pair in combinations(fields, 2)}
    require(len(witnesses) == len(expected) and pairs == expected, "Missing pairwise comparisons")
    print(f"SymPy {sp.__version__}")
    print(f"Verified norm equations and quintic coefficients for {len(fields)-1} class-number-five rows.")
    print("Recovered the real cyclotomic polynomial from Phi_11 by elimination.")
    print(f"Verified {len(irreducibles)} irreducibility witnesses and all {len(pairs)} unordered pairs.")
    print(f"Factored {len(cache)} distinct polynomial/prime pairs. All listed reductions are squarefree.")


if __name__ == "__main__":
    main()
