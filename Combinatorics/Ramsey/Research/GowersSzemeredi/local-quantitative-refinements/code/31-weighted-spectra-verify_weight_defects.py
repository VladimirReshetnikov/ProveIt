#!/usr/bin/env python3
"""Reproduce exact weight examples and small numerical graph/transfer checks.

Standard library only.  Exact checks use fractions.Fraction and direct finite
convolution/quadruple counts, independently of Fourier formulas used in the
article.  The numerical sections use floating point and are explicitly labeled as
numerical evidence, not a proof or a formal verification.

Run from any directory:
    python code/verify_weight_defects.py
The default JSON destination is data/weight_defect_verification.json.
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
from fractions import Fraction as R
from pathlib import Path


def rat(x):
    """A JSON-friendly exact rational and its decimal approximation."""
    x = R(x)
    return {"exact": str(x), "decimal": float(x)}


def cyclic_energy(v):
    """N^-3 times weighted ordered additive quadruples in Z/N."""
    n = len(v)
    conv = [sum(v[x] * v[(s - x) % n] for x in range(n))
            for s in range(n)]
    return sum(x * x for x in conv) / n**3


def plane_energy(w):
    """N^-3 (not N^-6) normalization on Z/N x Z/N."""
    n = len(w)
    conv = [[sum(w[x][y] * w[(s - x) % n][(t - y) % n]
                 for x in range(n) for y in range(n))
             for t in range(n)] for s in range(n)]
    return sum(x * x for row in conv for x in row) / n**3


def cross_energy(v, u):
    """One opposite-side two-coset assignment, normalized by N^3."""
    n = len(v)
    rv = [sum(v[x] * v[(x - d) % n] for x in range(n))
          for d in range(n)]
    ru = [sum(u[x] * u[(x - d) % n] for x in range(n))
          for d in range(n)]
    return sum(a * b for a, b in zip(rv, ru)) / n**3


def exact_defect_case(name, w, slope):
    n = len(w)
    w = [[R(x) for x in row] for row in w]
    v = [w[h][slope * h % n] for h in range(n)]
    mean = sum(v) / n
    off = [[R(0) if k == slope * h % n else w[h][k]
            for k in range(n)] for h in range(n)]
    fibers = [[w[h][(slope * h + z) % n] for h in range(n)]
              for z in range(n)]
    masses = [sum(u) / n for u in fibers]
    inside = cyclic_energy([x - mean for x in v])
    outside = plane_energy(off)
    leakage = 4 * mean**2 * sum(x * x for x in masses[1:])
    defect = plane_energy(w) - mean**4
    remainder = defect - inside - outside - leakage

    # Recover the entire remainder by support-position classification.
    points = list(itertools.product(range(n), repeat=2))
    same_side = R(0)
    three_outside = R(0)
    one_outside = R(0)
    for a, b, c in itertools.product(points, repeat=3):
        d = ((a[0] + b[0] - c[0]) % n,
             (a[1] + b[1] - c[1]) % n)
        vertices = (a, b, c, d)
        pos = [i for i, (h, k) in enumerate(vertices)
               if k != slope * h % n]
        value = math.prod(w[h][k] for h, k in vertices) / n**3
        if len(pos) == 1:
            one_outside += value
        elif len(pos) == 2 and pos in ([0, 1], [2, 3]):
            same_side += value
        elif len(pos) == 3:
            three_outside += value
    extra_cross = 4 * sum(cross_energy(v, fibers[z])
                          - mean**2 * masses[z]**2
                          for z in range(1, n))
    assert one_outside == 0
    assert inside >= 0 and outside >= 0 and leakage >= 0
    assert extra_cross >= 0 and same_side >= 0 and three_outside >= 0
    assert remainder == extra_cross + same_side + three_outside
    assert defect >= inside + outside + leakage
    return {
        "name": name, "group": f"Z/{n}", "slope": slope,
        "weight": [[str(x) for x in row] for row in w],
        "mean_on_graph": rat(mean), "defect": rat(defect),
        "centered_graph_U2_power4": rat(inside),
        "off_graph_energy": rat(outside),
        "coset_leakage_lower_bound": rat(leakage),
        "nonnegative_remainder": rat(remainder),
        "remainder_decomposition": {
            "extra_opposite_side_correlation": rat(extra_cross),
            "same_side_two_outside": rat(same_side),
            "three_outside": rat(three_outside),
        },
        "status": "exact rational identity and inequality passed",
    }


def exact_weight_defects():
    cases = [
        ("dense unequal fibers", [[1, R(1, 3)], [R(1, 2), R(3, 4)]], 1),
        ("three quotient cosets", [
            [1, R(1, 4), 0],
            [R(1, 2), R(3, 4), R(1, 3)],
            [R(1, 5), R(2, 3), 1]], 1),
        ("graph only", [[0, 0, 0], [0, 0, 1], [0, R(1, 2), 0]], 2),
        ("constant coset weights", [[R(2, 3), R(1, 7)],
                                     [R(2, 3), R(1, 7)]], 0),
    ]
    return [exact_defect_case(*case) for case in cases]


def bent_examples():
    rows = []
    for dimension in (1, 2, 3):
        k = 2**dimension
        n = k**2
        a = R(1, k)
        points = list(itertools.product(range(k), repeat=2))
        bent = [(-1)**((x & y).bit_count()) for x, y in points]
        v = [R(1 + b, 2) for b in bent]  # Indicator weights, 0 <= w <= 1.
        mean = sum(v) / n
        fourier = [
            sum(v[j] * (-1)**(((x & u) ^ (y & z)).bit_count())
                for j, (x, y) in enumerate(points)) / n
            for u, z in points
        ]
        energy = sum(c**4 for c in fourier)
        expected_ratio = 1 + R(n - 1, n**2) / (1 + a)**4
        relative_l1 = sum(abs(x - mean) for x in v) / n / mean
        assert mean == (1 + a) / 2
        assert energy / mean**4 == expected_ratio
        assert relative_l1 == 1 - a
        # Independent direct convolution in the Boolean group at these sizes.
        lookup = dict(zip(points, v))
        convolution = [sum(lookup[x, y] * lookup[x ^ s, y ^ t]
                           for x, y in points) for s, t in points]
        assert sum(c*c for c in convolution) / n**3 == energy
        rows.append({
            "group": f"F2^{2 * dimension}", "N": n,
            "bounded_indicator_weight": True,
            "mean_on_graph": rat(mean), "energy": rat(energy),
            "relative_energy": rat(energy / mean**4),
            "relative_L1_distance": rat(relative_l1),
            "status": "exact Walsh transform and direct convolution agree",
        })
    return rows


def diffuse_formula(n, leakage):
    leakage = R(leakage)
    return ((1 + leakage)**4
            + (n - 1) * (1 - leakage / (n - 1))**4) / n


def diffuse_examples():
    direct = []
    for n in (2, 3, 5, 8, 16):
        leakage = R(1)
        quotient = [R(1)] + [leakage / (n - 1)] * (n - 1)
        # Quotient energy has counting normalization, hence the factor n^3.
        actual = n**3 * cyclic_energy(quotient)
        expected = diffuse_formula(n, leakage)
        assert actual == expected
        assert sum(quotient[1:]) == leakage
        direct.append({
            "N": n, "normalized_off_graph_mass": rat(leakage),
            "energy": rat(actual), "bounded_weight": max(quotient) <= 1,
            "status": "exact quotient convolution agrees with formula",
        })
    asymptotic = []
    for exponent in (1, 2, 3, 4):
        n = 2**(8 * exponent)
        leakage = R(2**exponent)  # L_N=N^(1/8) tends to infinity.
        energy = diffuse_formula(n, leakage)
        asymptotic.append({
            "N": n, "normalized_off_graph_mass": rat(leakage),
            "energy_defect": rat(energy - 1),
            "bounded_weight": leakage / (n - 1) <= 1,
            "status": "exact evaluation of the proved formula; no enumeration",
        })
    return {"direct_checks": direct, "growing_leakage_formula_values": asymptotic}


def sharp_graph_profiles():
    rows = []
    for t in (R(0), R(1, 10**6), R(1, 10**4), R(1, 2000), R(1, 800)):
        fidelity = 1 - t
        epsilon = 2 * fidelity * t
        score = fidelity**2 + t**2
        kappa = fidelity**4 + 14 * fidelity**2 * t**2 + t**4
        assert score == 1 - epsilon
        assert 1 - 2 * epsilon == (1 - 2 * t)**2
        assert 1 - kappa == 4 * fidelity * t * (1 - 4 * fidelity * t)
        assert epsilon <= R(1, 400)
        rows.append({
            "group": "Z/2", "infidelity_t": rat(t),
            "fidelity_F": rat(fidelity), "epsilon": rat(epsilon),
            "full_graph_score": rat(score), "critical_ratio_kappa": rat(kappa),
            "sharp_root_identity": "1-2 epsilon = (1-2t)^2",
            "status": "exact rational profile identities passed",
        })
    return rows


def inner(a, b):
    return sum(x.conjugate() * y for x, y in zip(a, b)) / len(a)


def norm(a):
    return math.sqrt(max(0.0, inner(a, a).real))


def cyclic_quadratic(k, slope, linear):
    return [cmath.exp(1j * math.pi * slope * x * (x - k) / k
                      + 2j * math.pi * linear * x / k)
            for x in range(k)]


def coset_quadratic_states(n):
    states = []
    for k in range(1, n + 1):
        if n % k:
            continue
        step = n // k
        for offset in range(step):
            for slope in range(k):
                for linear in range(k):
                    local = cyclic_quadratic(k, slope, linear)
                    state = [0j] * n
                    for j, value in enumerate(local):
                        state[offset + step * j] = math.sqrt(n / k) * value
                    states.append((state, k, slope, linear, offset))
    return states


def ambiguity(f):
    n = len(f)
    return [[abs(sum(f[x] * f[(x-h) % n].conjugate()
                     * cmath.exp(-2j * math.pi * k * x / n)
                     for x in range(n)) / n)**2
             for k in range(n)] for h in range(n)]


def numerical_graph_checks():
    """Three reproducible states per group; exhaust every selected graph."""
    rng = random.Random(20261006)
    tolerance = 5e-12
    results = []
    for n in (2, 3, 4):
        candidates = coset_quadratic_states(n)
        for index, noise in enumerate((1e-4, 1e-3, 1 / 800)):
            base = cyclic_quadratic(n, (index + 1) % n, index % n)
            g = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(n)]
            component = inner(base, g)
            g = [z - component * q for z, q in zip(g, base)]
            gnorm = norm(g)
            g = [z / gnorm for z in g]
            f = [math.sqrt(1-noise) * q + math.sqrt(noise) * z
                 for q, z in zip(base, g)]
            best = max(candidates, key=lambda row: abs(inner(row[0], f))**2)
            closest, support_size, slope, _, _ = best
            fidelity = abs(inner(closest, f))**2
            t = max(0.0, 1-fidelity)
            assert support_size == n
            assert abs(t-noise) < tolerance
            q = ambiguity(f)
            on_graph = [(slope*h) % n for h in range(n)]
            off_upper = 4 * fidelity * t
            on_lower = (fidelity-t)**2
            for h in range(n):
                assert q[h][on_graph[h]] + tolerance >= on_lower
                for k in range(n):
                    if k != on_graph[h]:
                        assert q[h][k] <= off_upper + tolerance
            min_slack = float("inf")
            eligible = 0
            checked = 0
            for phi in itertools.product(range(n), repeat=n):
                score = sum(q[h][phi[h]] for h in range(n)) / n
                epsilon = 1-score
                beta = sum(phi[h] != on_graph[h] for h in range(n)) / n
                lower = 2*fidelity*t + (1-8*fidelity*t)*beta
                slack = epsilon-lower
                assert slack >= -tolerance
                min_slack = min(min_slack, slack)
                if epsilon <= 1/400 + tolerance:
                    bound = (1-math.sqrt(max(0.0, 1-2*epsilon))) / 2
                    assert t <= bound + tolerance
                    assert beta <= epsilon + tolerance
                    eligible += 1
                checked += 1
            results.append({
                "group": f"Z/{n}", "state_index": index,
                "seed": 20261006, "infidelity": t,
                "enumerated_coset_phase_candidates": len(candidates),
                "enumerated_selected_graphs": checked,
                "high_score_graphs_with_epsilon_at_most_1_over_400": eligible,
                "minimum_joint_budget_slack": min_slack,
                "floating_point_tolerance": tolerance,
                "status": "numerical checks passed; not a universal proof",
            })
    return results


def numerical_coset_transfer_checks():
    """Check exact-coset TV by direct spectra and independent basis overlaps.

    The states include point masses, proper coset phases, and full-support
    phases.  For a fixed subgroup size and quadratic slope, varying the
    coset and linear phase gives the common orthonormal eigenbasis.  We
    compute its probabilities directly rather than recover them from q.
    """
    seed = 20261007
    rng = random.Random(seed)
    tolerance = 5e-12
    results = []
    for n in (2, 3, 4, 6):
        candidates = coset_quadratic_states(n)
        for support_size in range(1, n + 1):
            if n % support_size:
                continue
            slope = 1 % support_size
            offset = n // support_size - 1
            basis = [row for row in candidates
                     if row[1] == support_size and row[2] == slope]
            assert len(basis) == n
            for i, row in enumerate(basis):
                for j, other in enumerate(basis):
                    assert abs(inner(row[0], other[0]) - (i == j)) < tolerance
            base_index = next(i for i, row in enumerate(basis)
                              if row[3] == 0 and row[4] == offset)
            base = basis[base_index][0]
            base_q = ambiguity(base)
            subgroup = {(h, k) for h in range(n) for k in range(n)
                        if base_q[h][k] > 0.5}
            assert len(subgroup) == n
            base_spectrum_residual = max(
                abs(base_q[h][k] - ((h, k) in subgroup))
                for h in range(n) for k in range(n))
            assert base_spectrum_residual < tolerance

            for noise in (0.0, 1e-3, 0.2):
                tail = [complex(rng.gauss(0, 1), rng.gauss(0, 1))
                        for _ in range(n)]
                component = inner(base, tail)
                tail = [z - component * b for z, b in zip(tail, base)]
                tail_norm = norm(tail)
                tail = [z / tail_norm for z in tail]
                state = [math.sqrt(1-noise) * b + math.sqrt(noise) * z
                         for b, z in zip(base, tail)]
                q = ambiguity(state)
                probabilities = [abs(inner(row[0], state))**2
                                 for row in basis]
                fidelity = probabilities[base_index]
                tail_square_mass = sum(p*p for i, p in enumerate(probabilities)
                                       if i != base_index)
                purity = sum(p*p for p in probabilities)
                off_mass = sum(q[h][k] for h in range(n) for k in range(n)
                               if (h, k) not in subgroup) / n
                difference = [[(q[h][k] - base_q[h][k]) / n
                               for k in range(n)] for h in range(n)]
                tv = sum(abs(x) for row in difference for x in row) / 2
                # A linear functional on [0,1]^(n^2) is maximized by
                # selecting its positive coefficients (or its negatives).
                supremum = max(sum(max(x, 0.0) for row in difference for x in row),
                               sum(max(-x, 0.0) for row in difference for x in row))
                identity_residual = max(
                    base_spectrum_residual,
                    abs(sum(probabilities) - 1),
                    abs(sum(x for row in q for x in row) / n - 1),
                    abs(fidelity - (1-noise)),
                    abs(tv - off_mass),
                    abs(tv - (1-purity)),
                    abs(tv - (1-fidelity**2-tail_square_mass)),
                    abs(supremum-tv),
                )
                assert identity_residual < tolerance

                weights = [
                    [[0.0 for _ in range(n)] for _ in range(n)],
                    [[1.0 for _ in range(n)] for _ in range(n)],
                    [[float((h, k) in subgroup) for k in range(n)]
                     for h in range(n)],
                    [[float((h, k) not in subgroup) for k in range(n)]
                     for h in range(n)],
                ]
                weights.extend([[rng.random() for _ in range(n)]
                                for _ in range(n)] for _ in range(12))
                min_slack = float("inf")
                attained = []
                for index, weight in enumerate(weights):
                    score_difference = abs(sum(weight[h][k] * difference[h][k]
                                               for h in range(n) for k in range(n)))
                    min_slack = min(min_slack, off_mass - score_difference)
                    assert score_difference <= off_mass + tolerance
                    assert score_difference <= 1-fidelity**2 + tolerance
                    if index in (2, 3):
                        attained.append(abs(score_difference - tv))
                assert max(attained) < tolerance
                results.append({
                    "group": f"Z/{n}", "support_size": support_size,
                    "coset_offset": offset, "quadratic_slope": slope,
                    "target_infidelity": noise, "fidelity_F": fidelity,
                    "tail_square_mass_A": tail_square_mass,
                    "joint_eigenbasis_purity": purity,
                    "off_subgroup_probability": off_mass,
                    "total_variation": tv,
                    "sup_bounded_weight_score_difference": supremum,
                    "maximum_identity_residual": identity_residual,
                    "tested_bounded_weights": len(weights),
                    "minimum_transfer_slack": min_slack,
                    "indicator_attainment_residual": max(attained),
                    "status": "numerical identity and transfer checks passed; not a universal proof",
                })
    return {
        "seed": seed, "floating_point_tolerance": tolerance,
        "checked_state_count": len(results),
        "checked_weight_count": sum(row["tested_bounded_weights"] for row in results),
        "maximum_identity_residual": max(row["maximum_identity_residual"] for row in results),
        "maximum_transfer_violation": max(0.0, -min(row["minimum_transfer_slack"] for row in results)),
        "identity": "sup_{0<=w<=1}|Theta_w(v)-Theta_w(psi)| = TV = off-H mass = 1-sum p^2 = 1-F^2-A",
        "cases": results,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent.parent
                        / "data" / "weight_defect_verification.json")
    args = parser.parse_args()
    report = {
        "title": "Weight defects, stability obstructions, and graph refinements",
        "arithmetic_note": "Sections marked exact use rational arithmetic; sections marked numerical use floating point.",
        "exact_weight_defects": exact_weight_defects(),
        "exact_bent_weight_obstruction": bent_examples(),
        "exact_diffuse_leakage_obstruction": diffuse_examples(),
        "exact_sharp_graph_profiles": sharp_graph_profiles(),
        "numerical_graph_checks": numerical_graph_checks(),
        "numerical_coset_transfer_checks": numerical_coset_transfer_checks(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("Passed: 4 exact defect decompositions, 3 exact bent examples,")
    print("5 exact quotient-convolution checks, 5 exact sharp graph profiles,")
    print("and 861 numerical selected-graph checks on 9 small-group states.")
    transfer = report["numerical_coset_transfer_checks"]
    print(f"Passed: {transfer['checked_state_count']} coset-transfer states and "
          f"{transfer['checked_weight_count']} bounded-weight checks;")
    print(f"maximum identity residual {transfer['maximum_identity_residual']:.3g}, "
          f"maximum transfer violation {transfer['maximum_transfer_violation']:.3g}.")
    print(f"JSON: {args.output}")


if __name__ == "__main__":
    main()
