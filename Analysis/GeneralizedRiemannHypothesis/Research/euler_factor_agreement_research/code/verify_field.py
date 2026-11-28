#!/usr/bin/env python3
"""Exact arithmetic checks for an explicit H_27 extension of Q(omega).

The mathematical proof that this quotient algebra is a field is in the paper:
it uses valuations above 2 and 7 and a Kummer eigenspace argument. This script
checks the algebraic identities and all 27 automorphisms in the 54-dimensional
Q-algebra with omega^2+omega+1=x^3-6=y^3-7=0 and
z^3=(1+x)^2(1+omega*x). Only Python's standard library is used.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def clean(a):
    return {k: v for k, v in a.items() if v}


def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
    return clean(out)


def scale(a, c):
    return clean({k: F(c) * v for k, v in a.items()})


def neg(a):
    return scale(a, -1)


def sub(a, b):
    return add(a, neg(b))


ONE = {(0, 0, 0, 0): F(1)}
OMEGA = {(1, 0, 0, 0): F(1)}
X = {(0, 1, 0, 0): F(1)}
Y = {(0, 0, 1, 0): F(1)}
Z = {(0, 0, 0, 1): F(1)}
GEN = (X, Y, Z)
# (1+x)^2(1+omega*x), reduced using x^3=6.
BETA = {
    (0, 0, 0, 0): F(1), (1, 0, 0, 0): F(6),
    (0, 1, 0, 0): F(2), (1, 1, 0, 0): F(1),
    (0, 2, 0, 0): F(1), (1, 2, 0, 0): F(2),
}


def reduce_term(exponents, coefficient, out):
    o, x, y, z = exponents
    if z >= 3:
        for (bo, bx, by, bz), bv in BETA.items():
            reduce_term((o+bo, x+bx, y+by, z-3+bz), coefficient*bv, out)
        return
    coefficient *= F(6)**(x//3) * F(7)**(y//3)
    x %= 3
    y %= 3
    o %= 3
    if o == 2:
        reduce_term((0, x, y, z), -coefficient, out)
        reduce_term((1, x, y, z), -coefficient, out)
    else:
        k = (o, x, y, z)
        out[k] = out.get(k, F(0)) + coefficient


def mul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            reduce_term(tuple(i+j for i, j in zip(ka, kb)), va*vb, out)
    return clean(out)


def power(a, k):
    out = ONE
    for _ in range(k):
        out = mul(out, a)
    return out


def apply(phi, a):
    bases = (OMEGA,) + tuple(phi)
    powers = [[power(b, i) for i in range(3)] for b in bases]
    out = {}
    for exp, coeff in a.items():
        term = ONE
        for j, e in enumerate(exp):
            term = mul(term, powers[j][e])
        out = add(out, scale(term, coeff))
    return out


def compose(phi, psi):
    """phi after psi, evaluated on the three generators."""
    return tuple(apply(phi, a) for a in psi)


def map_power(phi, k):
    out = GEN
    for _ in range(k):
        out = compose(phi, out)
    return out


def key(phi):
    return tuple(tuple(sorted(a.items())) for a in phi)


def check_map(phi):
    xx, yy, zz = phi
    return (power(xx, 3) == scale(ONE, 6)
            and power(yy, 3) == scale(ONE, 7)
            and power(zz, 3) == apply(phi, BETA))


def main():
    alpha = add(ONE, X)
    alpha_inverse = scale(add(sub(ONE, X), power(X, 2)), F(1, 7))
    sigma = (mul(OMEGA, X), Y, mul(mul(Y, Z), alpha_inverse))
    tau = (X, mul(OMEGA, Y), Z)
    kappa = (X, Y, mul(OMEGA, Z))
    norm = mul(mul(alpha, apply(sigma, alpha)), apply(map_power(sigma, 2), alpha))
    assert norm == scale(ONE, 7)
    assert mul(alpha, alpha_inverse) == ONE
    assert power(Z, 3) == mul(power(alpha, 2), add(ONE, mul(OMEGA, X)))
    assert mul(apply(sigma, BETA), power(alpha, 3)) == scale(BETA, 7)
    polynomial_coefficients = {18: 1, 15: 12, 12: 195, 9: 2212,
                               6: 9555, 3: 28812, 0: 117649}
    polynomial_value = {}
    for exponent, coefficient in polynomial_coefficients.items():
        polynomial_value = add(polynomial_value, scale(power(Z, exponent), coefficient))
    assert polynomial_value == {}
    for phi in (sigma, tau, kappa):
        assert check_map(phi)
        assert map_power(phi, 3) == GEN
    assert compose(tau, sigma) == compose(kappa, compose(sigma, tau))
    assert compose(kappa, sigma) == compose(sigma, kappa)
    assert compose(kappa, tau) == compose(tau, kappa)
    maps = [compose(map_power(sigma, a), compose(map_power(tau, b), map_power(kappa, c)))
            for a, b, c in product(range(3), repeat=3)]
    assert len(set(map(key, maps))) == 27
    assert all(check_map(phi) for phi in maps)
    assert all(map_power(phi, 3) == GEN for phi in maps)
    roots = [r for r in range(7) if r**3 % 7 == 6]
    residue_checks = []
    for omega in (2, 4):
        zeros = [[int((1 + pow(omega, i, 7)*r) % 7 == 0)
                  for r in roots] for i in range(3)]
        assert all(sum(row) == 1 for row in zeros)
        assert all(sum(zeros[i][j] for i in range(3)) == 1 for j in range(3))
        residue_checks.append({"omega_mod_7": omega, "roots_x_cubed_6": roots,
                               "alpha_conjugates_zero_matrix": zeros})
    obstruction = [[(a-k) % 3 for a in (2, 1, 0)] for k in range(3)]
    assert all(row != [0, 0, 0] for row in obstruction)
    result = {
        "status": "PASS",
        "arithmetic": "exact rational arithmetic; no floating point",
        "base_field": "Q(omega), omega^2+omega+1=0",
        "equations": ["x^3=6", "y^3=7", "z^3=(1+x)^2(1+omega*x)"],
        "norm_one_plus_x": 7,
        "rational_polynomial_for_z": "T^18+12T^15+195T^12+2212T^9+9555T^6+28812T^3+117649",
        "rational_polynomial_vanishes_at_z": True,
        "sigma_beta_times_alpha_cubed_equals_7_beta": True,
        "tau_sigma_equals_kappa_sigma_tau": True,
        "distinct_automorphisms": 27,
        "all_preserve_relations": True,
        "all_cube_to_identity": True,
        "prime_7_residue_checks": residue_checks,
        "valuation_obstruction_mod_3": obstruction,
        "scope": "Algebraic identities checked. Field-degree argument uses the written valuation and Kummer proof.",
    }
    out = Path(__file__).resolve().parents[1] / "results" / "explicit_field_checks.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
