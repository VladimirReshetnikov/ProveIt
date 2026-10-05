#!/usr/bin/env python3
"""Exact, finite checks for the presentation examples in the accompanying paper.

Usage:
    python verify_presentations.py
    python verify_presentations.py --output some_other_results.json

Requires Python 3.10+ and SymPy.  No floating-point linear algebra is used.
The program checks examples and identities; it is not a formal verification of
the general classification theorem, nor a certificate of literature novelty.

For an integer relation matrix R with r columns, it computes:
    g = r - rank_Q(R),
    K = {w in Q^r : R w = 0 and w >= 0},
    d = dimension_Q span(K).
The extreme rays of K are found by exhaustive support enumeration.  A support
S carries an extreme ray exactly when R[:, S] has a one-dimensional nullspace
whose generator has strictly positive entries after a possible sign change.
Primitive integer representatives provide exact certificates for these rays.
This method uses up to 2**r - 1 nullspace calculations, so it is intended for
small examples, rather than large-scale presentations.

The atom-cardinality labels in the JSON are consequences predicted by the
paper's theorem from (g, d), rather than counts obtained by enumerating atoms.
An independent cyclic-orbit enumeration of weak compositions checks the
power-relation counting formula, including noncoprime cases and stabilizers.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
from fractions import Fraction
from pathlib import Path

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


def relation_matrix(rows: list[list[int]], generators: int) -> sp.Matrix:
    """Construct R without losing its column count when there are no relations."""
    if generators < 1:
        raise ValueError("At least one generator is required in these examples")
    if any(len(row) != generators for row in rows):
        raise ValueError("Each relation must have one entry per generator")
    if any(not isinstance(x, int) for row in rows for x in row):
        raise TypeError("Relation entries must be integers")
    return sp.Matrix(rows) if rows else sp.zeros(0, generators)


def primitive_positive_ray(vector: sp.Matrix) -> tuple[int, ...] | None:
    """Orient a strictly one-signed rational vector and clear denominators."""
    entries = list(vector)
    if all(q < 0 for q in entries):
        entries = [-q for q in entries]
    if not all(q > 0 for q in entries):
        return None
    denominator = math.lcm(*(int(sp.denom(q)) for q in entries))
    integer_entries = [int(q * denominator) for q in entries]
    divisor = math.gcd(*integer_entries)
    return tuple(value // divisor for value in integer_entries)


def nonnegative_kernel_rays(matrix: sp.Matrix) -> list[tuple[int, ...]]:
    """Enumerate all primitive rays of ker_Q(R) intersected with Q_+^r."""
    r = matrix.cols
    rays: set[tuple[int, ...]] = set()
    for size in range(1, r + 1):
        for support in itertools.combinations(range(r), size):
            restricted = matrix.extract(range(matrix.rows), support)
            nullspace = restricted.nullspace()
            if len(nullspace) != 1:
                continue
            local_ray = primitive_positive_ray(nullspace[0])
            if local_ray is None:
                continue
            ray = [0] * r
            for position, value in zip(support, local_ray):
                ray[position] = value
            ray_tuple = tuple(ray)
            assert any(ray_tuple) and min(ray_tuple) >= 0
            assert math.gcd(*ray_tuple) == 1
            assert matrix * sp.Matrix(ray_tuple) == sp.zeros(matrix.rows, 1)
            assert restricted.rank() == size - 1
            rays.add(ray_tuple)
    return sorted(rays)


def torsion_invariant_factors(matrix: sp.Matrix) -> list[int]:
    """Return the nontrivial finite cyclic factors of Z^r / rowspan_Z(R)."""
    if matrix.rows == 0:
        return []
    diagonal = smith_normal_form(matrix, domain=sp.ZZ)
    entries = [abs(int(diagonal[i, i]))
               for i in range(min(diagonal.rows, diagonal.cols))]
    nonzero = [entry for entry in entries if entry]
    assert len(nonzero) == matrix.rank()
    assert all(b % a == 0 for a, b in zip(nonzero, nonzero[1:]))
    return [entry for entry in nonzero if entry > 1]


def classify_by_theorem(g: int, d: int) -> str:
    if g == 0:
        assert d == 0
        return "finite"
    if d <= 1:
        return "countably_infinite"
    return "continuum"


def verify_presentation(example: dict) -> dict:
    matrix = relation_matrix(example["relations"], example["generators"])
    rank = int(matrix.rank())
    g = matrix.cols - rank
    rays = nonnegative_kernel_rays(matrix)
    ray_matrix = (sp.Matrix.hstack(*(sp.Matrix(ray) for ray in rays))
                  if rays else sp.zeros(matrix.cols, 0))
    d = int(ray_matrix.rank())
    torsion = torsion_invariant_factors(matrix)
    cardinality = classify_by_theorem(g, d)
    assert 0 <= d <= g
    assert (g, d) == tuple(example["expected_g_d"]), example["name"]
    assert cardinality == example["expected_cardinality"], example["name"]
    assert torsion == example["expected_torsion"], example["name"]
    return {
        "name": example["name"],
        "generators": matrix.cols,
        "relations": example["relations"],
        "relation_rank_over_Q": rank,
        "group_free_rank_g": g,
        "group_torsion_invariant_factors": torsion,
        "group_order_if_finite": math.prod(torsion) if g == 0 else None,
        "primitive_nonnegative_kernel_rays": [list(ray) for ray in rays],
        "effective_irreversible_dimension_d": d,
        "atom_cardinality_predicted_by_theorem": cardinality,
        "expected_values_verified": True,
    }


PRESENTATIONS = [
    {"name": "free N", "generators": 1, "relations": [],
     "expected_g_d": [1, 1], "expected_torsion": [],
     "expected_cardinality": "countably_infinite"},
    {"name": "free N^2", "generators": 2, "relations": [],
     "expected_g_d": [2, 2], "expected_torsion": [],
     "expected_cardinality": "continuum"},
    {"name": "free N^3", "generators": 3, "relations": [],
     "expected_g_d": [3, 3], "expected_torsion": [],
     "expected_cardinality": "continuum"},
    {"name": "Z, presented by x+y=0", "generators": 2,
     "relations": [[1, 1]], "expected_g_d": [1, 0],
     "expected_torsion": [], "expected_cardinality": "countably_infinite"},
    {"name": "Z x N", "generators": 3, "relations": [[1, 1, 0]],
     "expected_g_d": [2, 1], "expected_torsion": [],
     "expected_cardinality": "countably_infinite"},
    {"name": "Z x N^2", "generators": 4, "relations": [[1, 1, 0, 0]],
     "expected_g_d": [3, 2], "expected_torsion": [],
     "expected_cardinality": "continuum"},
    {"name": "f^2=g^3", "generators": 2, "relations": [[2, -3]],
     "expected_g_d": [1, 1], "expected_torsion": [],
     "expected_cardinality": "countably_infinite"},
    {"name": "f^3=g^5", "generators": 2, "relations": [[3, -5]],
     "expected_g_d": [1, 1], "expected_torsion": [],
     "expected_cardinality": "countably_infinite"},
    {"name": "f^2=g^4", "generators": 2, "relations": [[2, -4]],
     "expected_g_d": [1, 1], "expected_torsion": [2],
     "expected_cardinality": "countably_infinite"},
    {"name": "f^2=g^3 h", "generators": 3, "relations": [[2, -3, -1]],
     "expected_g_d": [2, 2], "expected_torsion": [],
     "expected_cardinality": "continuum"},
    {"name": "fg=1", "generators": 2, "relations": [[1, 1]],
     "expected_g_d": [1, 0], "expected_torsion": [],
     "expected_cardinality": "countably_infinite"},
    {"name": "f^2=g^2 and fg=1", "generators": 2,
     "relations": [[2, -2], [1, 1]], "expected_g_d": [0, 0],
     "expected_torsion": [4], "expected_cardinality": "finite"},
    {"name": "noncancellative f+h=g+h", "generators": 3,
     "relations": [[1, -1, 0]], "expected_g_d": [2, 2],
     "expected_torsion": [], "expected_cardinality": "continuum"},
    {"name": "idempotent h+h=h", "generators": 1, "relations": [[1]],
     "expected_g_d": [0, 0], "expected_torsion": [],
     "expected_cardinality": "finite"},
]


def normalized_two_generator_ideals(m: int, n: int) -> dict:
    """Exhaust all I subset N with 0 in I, I+m subset I, I+n subset I.

    For coprime positive m,n every such I contains <m,n>, and is determined
    by which of the finitely many gaps it contains.  Membership in <m,n> is
    decided exactly using the Apéry representative b*n in each residue mod m,
    where 0 <= b < m.  Gap subsets are checked directly for both closures.
    """
    if min(m, n) <= 1 or math.gcd(m, n) != 1:
        raise ValueError("Use coprime m,n greater than one")
    apery = [0] * m
    for b in range(m):
        apery[(b * n) % m] = b * n

    def in_semigroup(k: int) -> bool:
        return k >= 0 and k >= apery[k % m]

    conductor = (m - 1) * (n - 1)
    gaps = [k for k in range(conductor) if not in_semigroup(k)]
    assert gaps[-1] == conductor - 1
    assert len(gaps) * 2 == conductor
    # These m consecutive members also certify closure beyond the conductor.
    assert all(in_semigroup(k) for k in range(conductor, conductor + m))
    gap_set = set(gaps)
    admissible: list[list[int]] = []
    histogram: dict[int, int] = {}
    for bits in itertools.product((False, True), repeat=len(gaps)):
        included_gaps = {gap for gap, bit in zip(gaps, bits) if bit}
        if all((gap + step not in gap_set or gap + step in included_gaps)
               for gap in included_gaps for step in (m, n)):
            admissible.append(sorted(included_gaps))
            size = len(included_gaps)
            histogram[size] = histogram.get(size, 0) + 1
    numerator = math.comb(m + n, m)
    assert numerator % (m + n) == 0
    rational_catalan = numerator // (m + n)
    assert len(admissible) == rational_catalan, (m, n)
    return {
        "m": m,
        "n": n,
        "conductor": conductor,
        "gaps_of_semigroup": gaps,
        "apery_representatives_indexed_by_residue_mod_m": apery,
        "gap_subsets_examined": 2 ** len(gaps),
        "normalized_ideals_count": len(admissible),
        "rational_catalan_count": rational_catalan,
        "count_by_number_of_included_gaps": {
            str(size): histogram[size] for size in sorted(histogram)
        },
        "admissible_included_gap_sets": sorted(admissible,
                                                key=lambda a: (len(a), a)),
        "expected_values_verified": True,
    }


def weak_compositions(total: int, parts: int):
    """Generate ordered nonnegative integer tuples of a fixed length and sum."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_compositions(total - first, parts - 1):
            yield (first,) + rest


def verify_cyclic_compositions(a: int, b: int) -> dict:
    """Enumerate rotation orbits independently of the divisor-sum formula.

    Each weak composition of b into a parts is reduced to the lexicographically
    least rotation.  Its local symmetry delta is the number of rotations that
    fix it.  We compare the orbit count both with the direct Burnside average
    and with N(a,b) = (a+b)^(-1) sum_{r|gcd(a,b)} phi(r)
                                            * binom((a+b)/r, a/r).
    Fractions are evaluated exactly, without truncated integer division.
    """
    if min(a, b) < 1:
        raise ValueError("a and b must be positive")
    orbit_stabilizers: dict[tuple[int, ...], int] = {}
    by_composition: dict[int, int] = {}
    fixed_by_rotation = [0] * a
    total = 0
    for composition in weak_compositions(b, a):
        total += 1
        assert len(composition) == a and sum(composition) == b
        rotations = [composition[shift:] + composition[:shift]
                     for shift in range(a)]
        delta = 0
        for shift, rotated in enumerate(rotations):
            if rotated == composition:
                delta += 1
                fixed_by_rotation[shift] += 1
        assert delta >= 1 and math.gcd(a, b) % delta == 0
        assert len(set(rotations)) * delta == a
        canonical = min(rotations)
        if canonical in orbit_stabilizers:
            assert orbit_stabilizers[canonical] == delta
        orbit_stabilizers[canonical] = delta
        by_composition[delta] = by_composition.get(delta, 0) + 1
    assert total == math.comb(a + b - 1, a - 1)
    by_orbit: dict[int, int] = {}
    for delta in orbit_stabilizers.values():
        by_orbit[delta] = by_orbit.get(delta, 0) + 1
    assert sum(by_orbit.values()) == len(orbit_stabilizers)
    assert sum(by_composition.values()) == total
    for delta, orbit_count in by_orbit.items():
        assert by_composition[delta] == orbit_count * (a // delta)

    terms = []
    for r_symbolic in sp.divisors(math.gcd(a, b)):
        r = int(r_symbolic)
        totient = int(sp.totient(r))
        coefficient = math.comb((a + b) // r, a // r)
        terms.append({"r": r, "phi_r": totient,
                      "binomial_coefficient": coefficient,
                      "contribution": totient * coefficient})
    numerator = sum(term["contribution"] for term in terms)
    divisor_sum = Fraction(numerator, a + b)
    direct_burnside = Fraction(sum(fixed_by_rotation), a)
    assert divisor_sum.denominator == direct_burnside.denominator == 1
    assert len(orbit_stabilizers) == divisor_sum == direct_burnside
    return {
        "a": a,
        "b": b,
        "gcd": math.gcd(a, b),
        "weak_compositions_enumerated": total,
        "cyclic_orbits_enumerated": len(orbit_stabilizers),
        "fixed_compositions_by_rotation_shift": fixed_by_rotation,
        "direct_burnside_average": str(direct_burnside),
        "divisor_sum_terms": terms,
        "divisor_sum_numerator": numerator,
        "divisor_sum_denominator": a + b,
        "divisor_sum_exact_value": str(divisor_sum),
        "stabilizer_order_delta_distribution_by_orbit": {
            str(delta): by_orbit[delta] for delta in sorted(by_orbit)
        },
        "stabilizer_order_delta_distribution_by_composition": {
            str(delta): by_composition[delta] for delta in sorted(by_composition)
        },
        "all_delta_divide_gcd": True,
        "orbit_stabilizer_identity_verified": True,
        "expected_values_verified": True,
    }


def verify_power_relation_totals(cyclic_checks: list[dict]) -> list[dict]:
    """Compute the article's total number of infinite types from checked N's.

    For g = gcd(m,n), the claimed total is tau(g) + sum_{e|g} N(m/e,n/e).
    The orbit summands have been independently enumerated.  Interpreting the
    formula as a classification of infinite types still uses the paper's proof.
    """
    counts = {(check["a"], check["b"]): check["cyclic_orbits_enumerated"]
              for check in cyclic_checks}
    examples = {(2, 3): 3, (2, 2): 5, (2, 4): 6,
                (3, 3): 7, (3, 6): 13, (4, 4): 16}
    results = []
    for (m, n), expected in examples.items():
        g = math.gcd(m, n)
        divisors = [int(e) for e in sp.divisors(g)]
        summands = [{"e": e, "a": m // e, "b": n // e,
                     "enumerated_N": counts[m // e, n // e]}
                    for e in divisors]
        total = len(divisors) + sum(item["enumerated_N"] for item in summands)
        assert total == expected
        results.append({
            "m": m,
            "n": n,
            "gcd_g": g,
            "tau_g": len(divisors),
            "nonbijective_summands": summands,
            "total_infinite_types_predicted_by_theorem": total,
            "expected_total": expected,
            "expected_values_verified": True,
        })
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    examples = [verify_presentation(example) for example in PRESENTATIONS]
    semigroup_checks = [normalized_two_generator_ideals(m, n)
                        for m, n in [(2, 3), (3, 4), (3, 5), (4, 5), (4, 7)]]
    cyclic_checks = [verify_cyclic_compositions(a, b)
                    for a in range(1, 9) for b in range(1, 9)]
    power_relation_totals = verify_power_relation_totals(cyclic_checks)
    result = {
        "purpose": "Exact finite checks accompanying the article",
        "scope": ("The general theorem is proved in the article. This script "
                  "does not formally verify that proof or establish novelty. "
                  "Cardinality labels are deductions from the theorem."),
        "arithmetic": "Exact integer and rational arithmetic throughout",
        "runtime": {"python": platform.python_version(),
                    "sympy": sp.__version__},
        "presentation_algorithm": ("Exhaust every nonempty column support; "
            "retain its one-dimensional kernel if it has a strictly positive "
            "generator; clear denominators and divide by the gcd; compute "
            "the rational rank of the resulting primitive rays. Smith normal "
            "form determines group-completion torsion."),
        "presentation_examples": examples,
        "normalized_semigroup_ideal_checks": semigroup_checks,
        "cyclic_composition_checks": cyclic_checks,
        "power_relation_infinite_type_totals": power_relation_totals,
        "all_assertions_passed": True,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {len(examples)} presentation examples with exact arithmetic.")
    print("Normalized ideal counts: " + ", ".join(
        f"({item['m']},{item['n']}): {item['normalized_ideals_count']}"
        for item in semigroup_checks))
    print(f"Verified {len(cyclic_checks)} cyclic-composition pairs (1 <= a,b <= 8).")
    print("Power-relation infinite type totals: " + ", ".join(
        f"({item['m']},{item['n']}): "
        f"{item['total_infinite_types_predicted_by_theorem']}"
        for item in power_relation_totals))
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
