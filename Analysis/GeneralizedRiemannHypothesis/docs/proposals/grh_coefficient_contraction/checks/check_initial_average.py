#!/usr/bin/env python3
"""Exact finite regression for collapse of the first-column gauge average.

The reduced gauge group is GL_1(Z/4q)^2 x GL_2(Z/4), m=2.
False ranks are (1,1,2), true ranks (2,2,3); the last edges are rectangular.
Both endpoints are anchored, and the initial true gauge is diag(g_false,0,1).
All arithmetic is integral modulo finite rings, with character values +/-1.
This verifies finite algebraic models, not Lean or the analytic GRH proof.
"""
from collections import defaultdict
from itertools import product
from math import gcd
import json


def mm(a, b, rows, inner, cols, modulus):
    return tuple(sum(a[i*inner+k]*b[k*cols+j] for k in range(inner)) % modulus
                 for i in range(rows) for j in range(cols))


def inv2(a, modulus=4):
    x, y, z, w = a
    di = pow((x*w-y*z) % modulus, -1, modulus)
    return tuple(v*di % modulus for v in (w, -y, -z, x))


def determinant(a, modulus=4):
    return (a[0]*a[3]-a[1]*a[2]) % modulus


def sign4(a):
    assert a % 4 in (1, 3)
    return 1 if a % 4 == 1 else -1


def legendre(a, q):
    if q == 1:
        return 1
    value = pow(a % q, (q-1)//2, q)
    assert value in (1, q-1)
    return 1 if value == 1 else -1


I2 = (1, 0, 0, 1)
E12 = (1, 0)
E23 = (1, 0, 0, 1, 0, 0)
STANDARD = ((1,), E12, I2, E23)
GL2 = [a for a in product(range(4), repeat=4) if gcd(determinant(a), 4) == 1]
assert len(GL2) == 96
INV2 = {a: inv2(a) for a in GL2}


def image_inverse(g, ring, triangle):
    """The observed standard tuple acted on by g^{-1}."""
    u, v, a = g
    lower0 = (v * pow(u, -1, triangle) % triangle,)
    lower1 = (pow(v, -1, triangle), 0)
    block_inverse = (pow(u, -1, 4), 0, 0, 1)
    upper0 = mm(a, block_inverse, 2, 2, 2, 4)
    upper1 = mm(E23, INV2[a], 3, 2, 2, 4)
    return (lower0, lower1, upper0, upper1)


def reaches_standard(observation, g, triangle):
    """Direct source-shaped predicate, separate from orbit accumulation."""
    low0, low1, high0, high1 = observation
    u, v, a = g
    if low0[0] * u * pow(v, -1, triangle) % triangle != 1:
        return False
    if tuple(x*v % triangle for x in low1) != E12:
        return False
    block = (u % 4, 0, 0, 1)
    if mm(mm(INV2[a], high0, 2, 2, 2, 4), block, 2, 2, 2, 4) != I2:
        return False
    return mm(high1, a, 3, 2, 2, 4) == E23


def good_character(g, q):
    u, v, a = g
    return sign4(u) * legendre(v, q) * sign4(determinant(a))


def bad_character(g, q):
    # Nontrivial on the residual congruence kernel: its averages must cancel.
    return good_character(g, q) * sign4(g[1])


def check_case(q):
    ring, triangle = 4*q, 2*q
    units = [u for u in range(ring) if gcd(u, ring) == 1]
    group = list(product(units, units, GL2))
    # Check the joint reductions used to force the shared initial gauge.
    assert len({(a % triangle, a % 4) for a in range(ring)}) == ring
    kernel = [u for u in units if u % triangle == 1]
    assert len(kernel) == 2
    # The character components are homomorphisms.
    for u, v in product(units, repeat=2):
        assert sign4(u*v) == sign4(u)*sign4(v)
        assert legendre(u*v, q) == legendre(u,q)*legendre(v,q)

    fibres = defaultdict(lambda: [0, 0, 0])
    for g in group:
        observation = image_inverse(g, ring, triangle)
        assert reaches_standard(observation, g, triangle)
        entry = fibres[observation]
        entry[0] += 1
        entry[1] += good_character(g, q)
        entry[2] += bad_character(g, q)
    h = len(kernel)
    d = len(GL2)  # The original unused true initial quotient.
    assert len(fibres)*h == len(group)
    for count, good_sum, bad_sum in fibres.values():
        assert count == h
        assert good_sum in (-h, h)
        assert bad_sum == 0
        assert d*good_sum in (-d*h, d*h)
        assert good_sum // h in (-1, 1)

    actual_stabilizer = {g for g in group if reaches_standard(STANDARD, g, triangle)}
    predicted_stabilizer = {(1, v, I2) for v in kernel}
    assert actual_stabilizer == predicted_stabilizer

    # Independently recompute a spread of full transporter sums using the
    # direct transformed-inclusion predicate, not dictionary fibre grouping.
    observations = list(fibres)
    sample_indices = sorted({0, len(observations)//7, len(observations)//3,
                             len(observations)//2, len(observations)-1})
    direct_count = 0
    for index in sample_indices:
        observation = observations[index]
        matching = [g for g in group if reaches_standard(observation, g, triangle)]
        assert [len(matching), sum(good_character(g,q) for g in matching),
                sum(bad_character(g,q) for g in matching)] == fibres[observation]
        direct_count += len(group)

    # Off-orbit examples: a rank defect, and an all-injective tuple that
    # violates the shared-node compatibility rather than injectivity.
    rank_bad = (STANDARD[0], (0, 0), STANDARD[2], STANDARD[3])
    coupling_bad = (STANDARD[0], STANDARD[1], (0, 1, 1, 0), STANDARD[3])
    for observation in (rank_bad, coupling_bad):
        assert observation not in fibres
        assert not any(reaches_standard(observation, g, triangle) for g in group)
        direct_count += len(group)

    return {
        "q": q, "grid_ring": f"Z/{ring}Z", "false_triangle_ring": f"Z/{triangle}Z",
        "true_triangle_ring": "Z/4Z", "false_ranks": [1,1,2], "true_ranks": [2,2,3],
        "reduced_group_order": len(group), "orbit_size": len(fibres),
        "stabilizer_cardinality": h, "redundant_slot_cardinality": d,
        "normalization_after_redundant_slot_removed": h,
        "normalization_for_original_average": d*h,
        "joint_reduction_injective": True,
        "explicit_stabilizer_identification": True,
        "all_nonempty_fibres_uniform": True,
        "good_normalized_values": sorted({v[1]//h for v in fibres.values()}),
        "nontrivial_stabilizer_character_all_zero": True,
        "direct_transporter_predicate_checks": direct_count,
        "off_orbit_tests": 2,
        "all_injective_incompatible_example_checked": True,
    }


def main():
    # Independently verify the determinant sign character on all GL2 products.
    for a, b in product(GL2, repeat=2):
        assert sign4(determinant(mm(a,b,2,2,2,4))) == \
               sign4(determinant(a))*sign4(determinant(b))
    cases = [check_case(q) for q in (1,3,5,7,11)]
    assert len({c["normalization_after_redundant_slot_removed"] for c in cases}) == 1
    assert len({c["normalization_for_original_average"] for c in cases}) == 1
    print(json.dumps({
        "status": "passed", "arithmetic": "Exact integer modular arithmetic; no floats",
        "scope": "Finite gauge-orbit models; not Lean compilation or analytic proof validation",
        "case_count": len(cases),
        "totals": {
            "gauge_elements_enumerated": sum(c["reduced_group_order"] for c in cases),
            "all_orbit_fibres_checked": sum(c["orbit_size"] for c in cases),
            "direct_transporter_predicate_checks": sum(c["direct_transporter_predicate_checks"] for c in cases),
            "GL2_character_multiplicativity_checks": len(GL2)**2,
            "off_orbit_tests": sum(c["off_orbit_tests"] for c in cases),
        }, "cases": cases,
    }, indent=2))


if __name__ == "__main__":
    main()
