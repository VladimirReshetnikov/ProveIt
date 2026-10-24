"""Exact checks of the homogeneous-index CRT closure lemma.

These finite checks do not replace the proof in HOMOGENEOUS_CLOSURE.md.
Python standard library only.  No assert statements: checks also run under -O.
"""

from fractions import Fraction
from itertools import product
from math import comb, factorial, gcd, prod
from pathlib import Path
import json
import random


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def evaluate(terms, index, coordinates):
    """terms maps (index exponent, coordinate exponents) to a coefficient."""
    return sum(coefficient * index ** powers[0]
               * prod(a ** b for a, b in zip(coordinates, powers[1:]))
               for powers, coefficient in terms.items())


def homogeneous(terms, s, coordinates):
    degree = max((powers[0] for powers in terms), default=0)
    return sum(coefficient * (1 - s) ** powers[0]
               * s ** (degree - powers[0])
               * prod(a ** b for a, b in zip(coordinates, powers[1:]))
               for powers, coefficient in terms.items())


def coefficient_majorant(terms, n, u):
    return sum(abs(coefficient) * n ** powers[0]
               * u ** sum(powers[1:])
               for powers, coefficient in terms.items()) + n + u + 1


def norm_tree(values, modulus=None):
    if len(values) == 1:
        result = values[0]
    else:
        cut = len(values) // 2
        a = norm_tree(values[:cut], modulus)
        b = norm_tree(values[cut:], modulus)
        result = a*a + b*b
    return result if modulus is None else result % modulus


def crt(residues, moduli):
    modulus = prod(moduli)
    return sum(r * (modulus // m) * pow(modulus // m, -1, m)
               for r, m in zip(residues, moduli)) % modulus


def prime(number):
    return number >= 2 and all(number % d for d in range(2, number)
                              if d*d <= number)


def main():
    checks = {}
    rng = random.Random(751023)
    examples = [
        {(0, 1): 1, (1, 0): -1},                # w-i
        {(0, 2): 1, (1, 1): -2, (2, 0): 1},    # (w-i)^2
        {(0, 1, 0): 1, (1, 0, 0): 1,
         (0, 0, 1): -1},                        # w1+i-w2
        {(3, 1): 2, (0, 2): -3, (1, 0): 7,
         (0, 0): -5},                           # mixed index degrees
        {(0, 2): 1, (0, 1): -1},                # degree zero in i
    ]

    count = 0
    for terms in examples:
        dimension = len(next(iter(terms))) - 1
        degree = max(powers[0] for powers in terms)
        for s in range(-7, 9):
            if s == 0:
                continue
            for _ in range(15):
                coordinates = [rng.randrange(-3, 4) for _ in range(dimension)]
                require(homogeneous(terms, s, coordinates)
                        == s**degree * evaluate(terms, Fraction(1-s, s), coordinates),
                        "homogenization is not an exact polynomial identity")
                count += 1
    checks["exact_rational_homogenization_cases"] = count

    count = 0
    for p in [3, 7, 11, 19, 23, 31, 43]:
        for s in range(1, p):
            index = (pow(s, -1, p) - 1) % p
            for terms in examples:
                dimension = len(next(iter(terms))) - 1
                degree = max(powers[0] for powers in terms)
                coordinates = [rng.randrange(p) for _ in range(dimension)]
                require((homogeneous(terms, s, coordinates)
                         - s**degree * evaluate(terms, index, coordinates)) % p == 0,
                        "affine index recovery failed modulo a prime")
                count += 1
    checks["modular_index_recovery_cases"] = count

    count = 0
    for h in range(2, 9):
        s = 4 * factorial(h)
        for n in range(1, h+1):
            moduli = [s*(i+1)-1 for i in range(n)]
            b = prod(moduli)
            q = (s*n)**n + 1
            big_m = s*q + 1
            require(all(gcd(a, c) == 1 for i, a in enumerate(moduli)
                        for c in moduli[i+1:]), "CRT moduli not coprime")
            require(b < big_m, "product exceeds reduction modulus")
            require((s**n * factorial(n) * comb(q+n, n)) % big_m == b,
                    "binomial product certificate failed")
            require(all(m % 4 == 3 for m in moduli), "inert residue absent")
            require(all(m % p for m in moduli for p in range(2, h+1)
                        if prime(p)), "a small prime divides a modulus")
            count += 1
    checks["exact_product_and_coprimality_cases"] = count

    count = 0
    for p in [3, 7, 11, 19]:
        for leaf_count in range(1, 5):
            for values in product(range(p), repeat=leaf_count):
                require((norm_tree(values, p) == 0) == all(v == 0 for v in values),
                        "nested norm anisotropy failed")
                count += 1
    checks["anisotropic_norm_finite_field_cases"] = count

    # Actual nonlinear-residual certificates.  First choose small row values,
    # then CRT-pack them.  All choices in [0,U] are tested against the local
    # equations.  Values U+1, U+2 deliberately violate the range conditions.
    count = 0
    successful = 0
    range_failures = 0
    residual_failures = 0
    max_modulus_bits = 0
    for terms in examples[:3] + examples[4:]:
        dimension = len(next(iter(terms))) - 1
        for n in range(1, 5):
            u = max(2, n)
            h = coefficient_majorant(terms, n, u)
            s = 4 * factorial(h)
            moduli = [s*(i+1)-1 for i in range(n)]
            b = prod(moduli)
            max_modulus_bits = max(max_modulus_bits, b.bit_length())
            candidates = []
            # Deliberately provide genuine families for each residual.
            if dimension == 2:
                candidates.append([[0, i] for i in range(n)])
            elif terms == examples[4]:
                candidates.append([[1] for i in range(n)])
            else:
                candidates.append([[i] for i in range(n)])
            for _ in range(55):
                candidates.append([[rng.randrange(u+3) for _ in range(dimension)]
                                   for i in range(n)])
            for rows in candidates:
                packed = [crt([row[j] for row in rows], moduli)
                          for j in range(dimension)]
                leaves = [comb(a, u+1) if a >= u+1 else 0 for a in packed]
                leaves.append(homogeneous(terms, s, packed))
                accepted = norm_tree(leaves, b) == 0
                in_range = all(0 <= a <= u for row in rows for a in row)
                residual_zero = all(evaluate(terms, i, row) == 0
                                    for i, row in enumerate(rows))
                require(accepted == (in_range and residual_zero),
                        "complete CRT fixture disagrees with exact local predicate")
                count += 1
                if accepted:
                    successful += 1
                elif not in_range:
                    range_failures += 1
                else:
                    residual_failures += 1
    checks["whole_certificate_cases"] = count
    checks["whole_certificate_successes"] = successful
    checks["whole_certificate_range_rejections"] = range_failures
    checks["whole_certificate_residual_rejections"] = residual_failures
    checks["largest_test_product_bits"] = max_modulus_bits

    # Negative controls for the three mathematical restrictions.
    require((1*1 + 2*2) % 5 == 0, "expected split-prime counterexample absent")
    require(sum(a*a for a in [1, 1, 1]) % 3 == 0
            and norm_tree([1, 1, 1], 3) != 0,
            "ordinary sums of three squares should not replace the nested norm")
    require(norm_tree([0, 7], 7) == 0, "expected large-residual alias absent")
    # Division by s modulo p is invalid if p divides s.
    terms = {(1, 0): 1}
    require(homogeneous(terms, 7, [0]) % 7 != 0
            and (7*evaluate(terms, 0, [0])) % 7 == 0,
            "expected nonunit counterexample absent")
    checks["negative_controls"] = 4
    checks["status"] = "all finite checks passed; universal claims use the written proof"
    output = Path(__file__).with_name("HOMOGENEOUS_CHECKS.json")
    output.write_text(json.dumps(checks, indent=2) + "\n")
    print(json.dumps(checks, indent=2))


if __name__ == "__main__":
    main()
