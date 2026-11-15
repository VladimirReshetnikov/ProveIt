#!/usr/bin/env python3
"""Finite symbolic checks accompanying the iPRA polynomial-formula report.

This script is evidence, not part of the trusted mathematical proof.  Every
check is an exact calculation over Z, finite fields, or the finite group S_5.
It writes a deterministic JSON report next to this file.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence

import sympy as sp


def poly_reduce(expr: sp.Expr, relations: Sequence[sp.Expr], variables: Sequence[sp.Symbol]) -> sp.Expr:
    """Return the reduced normal form modulo a Groebner basis."""
    gb = sp.groebner(list(relations), *variables, order="lex", domain=sp.QQ)
    return sp.expand(gb.reduce(sp.expand(expr))[1])


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Composition p o q, with permutations represented by image tuples."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def commutator(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return compose(compose(compose(a, b), inverse(a)), inverse(b))


def permutation_from_cycles(*cycles: Sequence[int], n: int = 5) -> tuple[int, ...]:
    p = list(range(n))
    for cycle in cycles:
        if not cycle:
            continue
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            p[a - 1] = b - 1
    return tuple(p)


def parity(p: tuple[int, ...]) -> int:
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j]) % 2


def subgroup_generated(generators: Iterable[tuple[int, ...]], n: int = 5) -> set[tuple[int, ...]]:
    identity = tuple(range(n))
    gens = set(generators)
    gens |= {inverse(g) for g in list(gens)}
    closure = {identity}
    changed = True
    while changed:
        changed = False
        for a in list(closure):
            for b in gens | closure:
                c = compose(a, b)
                if c not in closure:
                    closure.add(c)
                    changed = True
    return closure


def derived_subgroup(group: set[tuple[int, ...]]) -> set[tuple[int, ...]]:
    comms = {commutator(a, b) for a in group for b in group}
    return subgroup_generated(comms, n=len(next(iter(group))))


def cycle_type(p: tuple[int, ...]) -> list[int]:
    seen = [False] * len(p)
    sizes: list[int] = []
    for i in range(len(p)):
        if seen[i]:
            continue
        j = i
        size = 0
        while not seen[j]:
            seen[j] = True
            size += 1
            j = p[j]
        if size > 1:
            sizes.append(size)
    return sorted(sizes)


def main() -> None:
    # Quadratic factorization.
    a, b, c, s, X = sp.symbols("a b c s X")
    r_plus = (-b + s) / (2 * a)
    r_minus = (-b - s) / (2 * a)
    quadratic_error = sp.together(a * (X - r_plus) * (X - r_minus) - (a * X**2 + b * X + c))
    quadratic_num = sp.factor(sp.together(quadratic_error).as_numer_denom()[0])
    quadratic_reduced = sp.rem(sp.Poly(quadratic_num, s), sp.Poly(s**2 - (b**2 - 4*a*c), s)).as_expr()

    # Cubic Cardano factorization.
    p, q, u, v, w, Y = sp.symbols("p q u v w Y")
    roots3 = [u + v, w*u + w**2*v, w**2*u + w*v]
    cubic_product = sp.expand(sp.prod(Y - r for r in roots3))
    cubic_error = sp.expand(cubic_product - (Y**3 + p*Y + q))
    cubic_reduced = poly_reduce(
        cubic_error,
        [w**2 + w + 1, u*v + p/3, u**3 + v**3 + q],
        [w, u, v, p, q, Y],
    )

    # Ferrari factorization and resolvent compatibility.
    m, t, rho, sigma, r = sp.symbols("m t rho sigma r")
    ferrari_product = sp.expand((Y**2 - s*Y + (m-t)) * (Y**2 + s*Y + (m+t)))
    ferrari_error = sp.expand(ferrari_product - (Y**4 + p*Y**2 + q*Y + r))
    ferrari_reduced = poly_reduce(
        ferrari_error,
        [s**2 - (2*m-p), 2*s*t + q, t**2 - (m**2-r)],
        [s, t, m, p, q, r, Y],
    )
    resolvent = sp.expand(q**2 - 4*(2*m-p)*(m**2-r))
    monic_resolvent = sp.expand(m**3 - p*m**2/2 - r*m + p*r/2 - q**2/8)
    resolvent_relation = sp.simplify(resolvent + 8*monic_resolvent)

    # S5 and A5 derived subgroups, plus the explicit commutators used in the report.
    S5 = set(itertools.permutations(range(5)))
    A5 = {g for g in S5 if parity(g) == 0}
    dS5 = derived_subgroup(S5)
    dA5 = derived_subgroup(A5)
    transposition_a = permutation_from_cycles((2, 3))
    transposition_b = permutation_from_cycles((1, 2))
    even_a = permutation_from_cycles((2, 3), (4, 5))
    even_b = permutation_from_cycles((1, 2), (4, 5))
    comm_s5 = commutator(transposition_a, transposition_b)
    comm_a5 = commutator(even_a, even_b)
    target_123 = permutation_from_cycles((1, 2, 3))

    # Optional explicit rational quintic certificate.
    Z = sp.symbols("Z")
    quintic = Z**5 - Z - 1
    disc = int(sp.discriminant(quintic, Z))
    factor_mod2 = sp.factor_list(quintic, modulus=2)
    factor_mod3 = sp.factor_list(quintic, modulus=3)
    irreducible_quadratics_mod3 = [Z**2 + 1, Z**2 + Z + 2, Z**2 + 2*Z + 2]
    remainders_mod3 = [
        str(sp.rem(quintic, h, domain=sp.GF(3))) for h in irreducible_quadratics_mod3
    ]

    checks = {
        "quadratic_factorization_remainder": str(sp.expand(quadratic_reduced)),
        "cubic_factorization_groebner_remainder": str(cubic_reduced),
        "ferrari_factorization_groebner_remainder": str(ferrari_reduced),
        "resolvent_equals_minus_8_times_monic_resolvent": str(resolvent_relation),
        "S5_order": len(S5),
        "A5_order": len(A5),
        "derived_S5_order": len(dS5),
        "derived_S5_is_A5": dS5 == A5,
        "derived_A5_order": len(dA5),
        "derived_A5_is_A5": dA5 == A5,
        "commutator_transpositions_cycle_type": cycle_type(comm_s5),
        "commutator_transpositions_is_123": comm_s5 == target_123,
        "commutator_even_double_transpositions_cycle_type": cycle_type(comm_a5),
        "commutator_even_double_transpositions_is_123": comm_a5 == target_123,
        "x5_minus_x_minus_1_discriminant": disc,
        "x5_minus_x_minus_1_factor_mod_2": str(factor_mod2),
        "x5_minus_x_minus_1_factor_mod_3": str(factor_mod3),
        "remainders_against_monic_irreducible_quadratics_mod_3": remainders_mod3,
    }

    required_zero = [
        checks["quadratic_factorization_remainder"] == "0",
        checks["cubic_factorization_groebner_remainder"] == "0",
        checks["ferrari_factorization_groebner_remainder"] == "0",
        checks["resolvent_equals_minus_8_times_monic_resolvent"] == "0",
        checks["derived_S5_is_A5"],
        checks["derived_A5_is_A5"],
        checks["commutator_transpositions_is_123"],
        checks["commutator_even_double_transpositions_is_123"],
        disc == 2869,
    ]
    checks["all_required_checks_pass"] = all(required_zero)

    out = Path(__file__).with_name("verification_report.json")
    out.write_text(json.dumps(checks, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(checks, indent=2, sort_keys=True))
    if not checks["all_required_checks_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
