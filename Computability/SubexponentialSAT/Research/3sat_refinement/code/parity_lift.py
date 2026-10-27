#!/usr/bin/env python3
"""Exact parity lift and checks for the dense sparse-polynomial reduction.

This is a coefficient-arithmetic prototype, not a subexponential SAT solver.
An integer multilinear polynomial is {support_bitmask: coefficient}.
Multiplication reduces x_j**2 = x_j.  Only Python's standard library is used.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import time


def normalise_monomials(monomials):
    """Cancel repeated monomials over F_2; mask 0 denotes constant 1."""
    live = set()
    for mask in monomials:
        if mask < 0:
            raise ValueError("Monomial supports must be nonnegative bitmasks")
        if mask in live:
            live.remove(mask)
        else:
            live.add(mask)
    return tuple(sorted(live))


def add(a, b):
    result = dict(a)
    for support, value in b.items():
        result[support] = result.get(support, 0) + value
        if result[support] == 0:
            del result[support]
    return result


def multiply(a, b, modulus=None):
    """Multiply integer multilinear polynomials, optionally modulo modulus."""
    result = {}
    for sa, ca in a.items():
        for sb, cb in b.items():
            s = sa | sb
            result[s] = result.get(s, 0) + ca * cb
    if modulus is not None:
        result = {s: c % modulus for s, c in result.items()}
    return {s: c for s, c in result.items() if c}


def parity_indicator_poly(monomials):
    """Multilinear representative of (1 + prod(1-2m))/2 over Z."""
    product = {0: 1}
    for support in normalise_monomials(monomials):
        factor = add({0: 1}, {support: -2})
        product = multiply(product, factor)
    product = add(product, {0: 1})
    assert all(c % 2 == 0 for c in product.values())
    return {s: c // 2 for s, c in product.items() if c}


def evaluate(poly, assignment):
    return sum(c for support, c in poly.items()
               if support & assignment == support)


def parity_value(monomials, assignment):
    return sum(s & assignment == s for s in monomials) % 2


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            break
        sub = (sub - 1) & mask


def indicator_coefficient(monomials, support):
    """Direct Boolean Moebius inversion, requiring no auxiliary V."""
    monomials = normalise_monomials(monomials)
    degree = support.bit_count()
    return sum((-1 if (degree - sub.bit_count()) % 2 else 1)
               for sub in submasks(support)
               if parity_value(monomials, sub) == 0)


def v2(integer):
    if integer == 0:
        return math.inf
    absolute = abs(integer)
    return (absolute & -absolute).bit_length() - 1


def ordinary_multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def old_remainders(precision):
    """Source e_j in p_l(Y)=sum e_j(Y)*(Y^2-Y)^j, for comparison."""
    p = ordinary_multiply(
        [(-1)**i * math.comb(precision, i)
         for i in range(precision + 1)],
        [math.comb(precision + j - 1, j)
         for j in range(precision)])
    result = []
    while any(p):
        remainder = list(p)
        quotient = [0] * max(1, len(p) - 2)
        for degree in range(len(remainder) - 1, 1, -1):
            c = remainder[degree]
            quotient[degree - 2] += c
            remainder[degree] -= c
            remainder[degree - 1] += c
        result.append((remainder[0], remainder[1] if len(remainder) > 1 else 0))
        p = quotient
    result += [(0, 0)] * (precision - len(result))
    assert len(result) == precision
    return result


def old_local_coefficient(monomials, support, precision):
    """Source's length-p V vector for one indicated incidence monomial."""
    modulus = 1 << precision
    remainders = old_remainders(precision)
    result = [0] * precision
    monomials = normalise_monomials(monomials)
    for sub in submasks(support):
        sign = (-1 if (support.bit_count() - sub.bit_count()) % 2 else 1)
        y = sum(s & sub == s for s in monomials)
        h = y * (y - 1)
        power = 1
        for j, (constant, linear) in enumerate(remainders):
            result[j] = (result[j] + sign * (constant + linear * y) * power) % modulus
            power = power * h % modulus
    return result


def truncated_product(a, b, precision):
    modulus = 1 << precision
    result = [0] * precision
    for i, x in enumerate(a):
        for j, y in enumerate(b[:precision - i]):
            result[i + j] = (result[i + j] + x * y) % modulus
    return result


def count_by_multilinear_product(equations, variables):
    """Exponential-size reference only, independent of tensor contraction."""
    product = {0: 1}
    modulus = 1 << (variables + 1)
    for equation in equations:
        product = multiply(product, parity_indicator_poly(equation), modulus)
    return sum(c * (1 << (variables - support.bit_count()))
               for support, c in product.items()) % modulus


def count_by_assignments(equations, variables):
    return sum(all(parity_value(normalise_monomials(eq), x) == 0
                   for eq in equations)
               for x in range(1 << variables))


def run_checks(seed=20261026):
    start = time.perf_counter()
    rng = random.Random(seed)
    counts = {
        "exhaustive_polynomials": 0,
        "truth_table_comparisons": 0,
        "coefficient_and_valuation_checks": 0,
        "random_system_count_comparisons": 0,
        "old_vs_new_ring_products": 0,
        "incidence_degree_checks": 0,
        "tight_degree_examples": 0,
    }

    for variables, degree_bound in [(3, 3), (4, 2)]:
        basis = [s for s in range(1 << variables)
                 if s.bit_count() <= degree_bound]
        for choices in range(1 << len(basis)):
            monomials = tuple(s for i, s in enumerate(basis) if choices >> i & 1)
            polynomial = parity_indicator_poly(monomials)
            counts["exhaustive_polynomials"] += 1
            for assignment in range(1 << variables):
                assert evaluate(polynomial, assignment) == 1 - parity_value(monomials, assignment)
                counts["truth_table_comparisons"] += 1
            for support in range(1 << variables):
                coefficient = polynomial.get(support, 0)
                assert coefficient == indicator_coefficient(monomials, support)
                floor = max(0, (support.bit_count() + degree_bound - 1) // degree_bound - 1)
                assert v2(coefficient) >= floor
                counts["coefficient_and_valuation_checks"] += 1

    for _ in range(300):
        variables = rng.randrange(1, 7)
        degree_bound = min(3, variables)
        basis = [s for s in range(1 << variables)
                 if s.bit_count() <= degree_bound]
        equations = [rng.sample(basis, rng.randrange(min(len(basis), 8) + 1))
                     for _ in range(rng.randrange(7))]
        assert count_by_multilinear_product(equations, variables) == count_by_assignments(equations, variables)
        counts["random_system_count_comparisons"] += 1

    for _ in range(250):
        precision = rng.randrange(1, 7)
        modulus = 1 << precision
        old = [1] + [0] * (precision - 1)
        new = 1
        for _ in range(rng.randrange(1, 5)):
            variables = rng.randrange(1, 6)
            basis = [s for s in range(1 << variables) if s.bit_count() <= 3]
            equation = rng.sample(basis, rng.randrange(min(len(basis), 8) + 1))
            support = rng.randrange(1 << variables)
            old = truncated_product(old, old_local_coefficient(equation, support, precision), precision)
            new = new * indicator_coefficient(equation, support) % modulus
        assert sum(old) % modulus == new
        counts["old_vs_new_ring_products"] += 1

    for _ in range(120):
        precision = rng.randrange(1, 6)
        modulus = 1 << precision
        degree_bound = rng.randrange(1, 4)
        tests = rng.randrange(1, 4)
        incidence_product = {0: 1}
        offset = 0
        for _ in range(tests):
            variables = rng.randrange(1, 5)
            basis = [s for s in range(1 << variables)
                     if s.bit_count() <= degree_bound]
            equation = rng.sample(basis, rng.randrange(min(len(basis), 6) + 1))
            local = parity_indicator_poly(equation)
            lifted = {support << offset: coefficient for support, coefficient in local.items()}
            incidence_product = multiply(incidence_product, lifted, modulus)
            offset += variables
        cap = degree_bound * (precision + tests - 1)
        assert all(support.bit_count() <= cap for support in incidence_product)
        counts["incidence_degree_checks"] += 1

    for degree_bound in [1, 2, 3]:
        for precision in range(2, 6):
            tests = precision
            product = {0: 1}
            offset = 0
            # R = 2p-1 = p+a-1 selected disjoint monomials.
            for index in range(tests):
                number = 1 if index == 0 else 2
                equation = []
                for _ in range(number):
                    mask = ((1 << degree_bound) - 1) << offset
                    offset += degree_bound
                    equation.append(mask)
                product = multiply(product, parity_indicator_poly(equation))
            full = (1 << offset) - 1
            coefficient = product[full]
            assert offset == degree_bound * (precision + tests - 1)
            assert v2(coefficient) == precision - 1
            assert coefficient % (1 << precision) != 0
            counts["tight_degree_examples"] += 1

    # Explicit cancellation and constant-equation cases.
    assert parity_indicator_poly([1, 1]) == {0: 1}
    assert parity_indicator_poly([0]) == {}
    assert parity_indicator_poly([]) == {0: 1}
    assert count_by_multilinear_product([], 6) == 64

    return {
        "status": "all checks passed",
        "seed": seed,
        "counts": counts,
        "elapsed_seconds": round(time.perf_counter() - start, 6),
        "scope": "Finite tests of exact parity identities, coefficient divisibility, and ring replacement; not a test of the paper's complete subexponential solver.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261026)
    args = parser.parse_args()
    print(json.dumps(run_checks(args.seed), indent=2))


if __name__ == "__main__":
    main()
