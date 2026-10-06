#!/usr/bin/env python3
"""Exhaustive exact checks for the noisy parity puzzle.

Uses only the Python standard library.  No simulation, floating-point arithmetic,
SAT solver, repository code, or assertion based solely on a sampled truth table.

A Boolean rule is a truth table f : {0,1}^n -> {0,1}.  X is uniform, J is
independent with probabilities p_i, Z has independent Bernoulli(eta) bits, and
the score is P[f(X) != f(X xor e_J xor Z)].  The parameter range checked is
0 <= eta <= 1/2 with p_1 >= ... >= p_n >= 0 and sum p_i = 1.

Run: python3 verify_parity.py --output verification.json
"""

from __future__ import annotations

import argparse
from array import array
from collections import Counter
from fractions import Fraction
import json
from math import lcm
from pathlib import Path
import platform
import time


def rational(x: Fraction | int) -> str:
    """A JSON-safe, exact, human-readable rational number."""
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def truth_restrictions(f: int, n: int, coordinate: int) -> tuple[int, int]:
    """Remove coordinate i, keeping all other coordinates in their old order."""
    lo = (1 << coordinate) - 1
    f0 = f1 = 0
    for y in range(1 << (n - 1)):
        x0 = (y & lo) | ((y & ~lo) << 1)
        f0 |= ((f >> x0) & 1) << y
        f1 |= ((f >> (x0 | (1 << coordinate))) & 1) << y
    return f0, f1


def all_exact_tree_costs(max_n: int) -> list[list[int]]:
    """E[n][f] = 2^n times the minimum uniform expected query count.

    Each nonconstant exact decision tree queries a coordinate at its root. Its
    two restrictions occur with probability 1/2.  Exhausting every possible
    first coordinate therefore gives an exact dynamic program, not a bound.
    """
    levels = [[0, 0]]  # The two rules on the singleton 0-dimensional cube.
    for n in range(1, max_n + 1):
        cube_size = 1 << n
        rules = 1 << cube_size
        prev = levels[-1]
        costs = [0] * rules
        for f in range(1, rules - 1):
            candidates = []
            for i in range(n):
                f0, f1 = truth_restrictions(f, n, i)
                candidates.append(prev[f0] + prev[f1])
            costs[f] = cube_size + min(candidates)
        levels.append(costs)
    return levels


def walsh_numerators(f: int, n: int) -> list[int]:
    """Unnormalized Walsh transform of (-1)^f by integer butterflies."""
    h = [1 - 2 * ((f >> x) & 1) for x in range(1 << n)]
    stride = 1
    while stride < len(h):
        for start in range(0, len(h), stride << 1):
            for j in range(stride):
                u, v = h[start + j], h[start + j + stride]
                h[start + j], h[start + j + stride] = u + v, u - v
        stride <<= 1
    return h


def translated_truth_tables(n: int) -> list[array]:
    """For each d, list the tables x -> f(x xor d), for every f."""
    cube_size = 1 << n
    rules = 1 << cube_size
    bit_to_index = {1 << x: x for x in range(cube_size)}
    permutations = []
    for d in range(cube_size):
        values = array("H", [0]) * rules
        for f in range(1, rules):
            bit = f & -f
            values[f] = values[f ^ bit] | (1 << (bit_to_index[bit] ^ d))
        permutations.append(values)
    return permutations


def transition_integers(p: list[Fraction], eta: Fraction) -> tuple[list[int], int]:
    """Exact common-denominator distribution of D=e_J xor Z."""
    n = len(p)
    pd = lcm(*(x.denominator for x in p))
    u, v = eta.numerator, eta.denominator
    numerators = []
    for d in range(1 << n):
        weight = 0
        for i, pi in enumerate(p):
            h = (d ^ (1 << i)).bit_count()
            weight += int(pi * pd) * u**h * (v - u)**(n - h)
        numerators.append(weight)
    denominator = pd * v**n
    assert sum(numerators) == denominator
    return numerators, denominator


def setup_case(name: str, p: list[Fraction], eta: Fraction) -> dict:
    assert p == sorted(p, reverse=True)
    assert sum(p) == 1 and all(x >= 0 for x in p)
    assert 0 <= eta <= Fraction(1, 2)
    n = len(p)
    masses, denominator = transition_integers(p, eta)
    # These spectral score weights are computed from the transition kernel;
    # they are not taken on trust from the claimed closed formula.
    spectral = [sum(masses[d] for d in range(1 << n)
                    if (s & d).bit_count() % 2) for s in range(1 << n)]
    a = 1 - 2 * eta
    for s in range(1 << n):
        ps = sum(p[i] for i in range(n) if (s >> i) & 1)
        closed = (1 + a**s.bit_count() * (2 * ps - 1)) / 2
        assert Fraction(spectral[s], denominator) == closed
    top = [spectral[(1 << k) - 1] for k in range(n + 1)]
    first_max = top.index(max(top))
    # Check the monotonicity and concavity required for the budget envelope.
    increasing_deltas = [top[k + 1] - top[k] for k in range(first_max)]
    assert all(d > 0 for d in increasing_deltas)
    assert increasing_deltas == sorted(increasing_deltas, reverse=True)
    assert all(top[k + 1] <= top[k] for k in range(first_max, n))
    assert all(spectral[s] <= top[s.bit_count()] for s in range(1 << n))
    return dict(name=name, p=p, eta=eta, masses=masses,
                denominator=denominator, spectral=spectral, top=top,
                first_max=first_max, maximum=-1, maximizers=0,
                budget_equalities=0, minimum_positive_slack=None)


def cases_for_dimension(n: int) -> list[dict]:
    uniform = [Fraction(1, n)] * n
    geometric = [Fraction(2**(n - 1 - i), 2**n - 1) for i in range(n)]
    triangular = [Fraction(2 * (n - i), n * (n + 1)) for i in range(n)]
    point = [Fraction(1)] + [Fraction(0)] * (n - 1)
    specs = [(f"uniform_eta_{rational(eta)}", uniform, eta)
             for eta in [Fraction(0), Fraction(1, 10), Fraction(1, 4), Fraction(1, 2)]]
    specs.extend([
        ("geometric_eta_1/10", geometric, Fraction(1, 10)),
        ("geometric_eta_1/4", geometric, Fraction(1, 4)),
        ("triangular_eta_1/5", triangular, Fraction(1, 5)),
        ("point_mass_eta_1/4", point, Fraction(1, 4)),
    ])
    return [setup_case(*spec) for spec in specs]


def verify_dimension(n: int, costs: list[int]) -> dict:
    cube_size = 1 << n
    rules = 1 << cube_size
    permutations = translated_truth_tables(n)
    cases = cases_for_dimension(n)
    degree = [s.bit_count() for s in range(cube_size)]
    influence_tree_equalities = 0
    for f in range(rules):
        disagreements = [(f ^ permutations[d][f]).bit_count()
                         for d in range(cube_size)]
        h = walsh_numerators(f, n)
        h2 = [x*x for x in h]
        assert sum(h2) == cube_size**2, ("Parseval", n, f)
        influence_numerator = sum(disagreements[1 << i] for i in range(n))
        assert influence_numerator * cube_size == sum(
            degree[s] * h2[s] for s in range(cube_size)), ("influence", n, f)
        assert influence_numerator <= costs[f], ("tree/influence", n, f)
        influence_tree_equalities += influence_numerator == costs[f]
        for case in cases:
            direct = sum(m * b for m, b in zip(case["masses"], disagreements))
            fourier = sum(w * q for w, q in zip(case["spectral"], h2))
            assert direct * cube_size == fourier, ("direct/Fourier", n, f, case["name"])
            if direct > case["maximum"]:
                case["maximum"] = direct
                case["maximizers"] = 1
            elif direct == case["maximum"]:
                case["maximizers"] += 1
            kmax = case["first_max"]
            if costs[f] >= cube_size * kmax:
                bound = cube_size * case["top"][kmax]
            else:
                j, r = divmod(costs[f], cube_size)
                bound = ((cube_size - r) * case["top"][j]
                         + r * case["top"][j + 1])
            slack = bound - direct
            assert slack >= 0, ("budget envelope", n, f, case["name"])
            if slack == 0:
                case["budget_equalities"] += 1
            elif case["minimum_positive_slack"] is None or slack < case["minimum_positive_slack"]:
                case["minimum_positive_slack"] = slack
    out_cases = []
    for case in cases:
        den = case["denominator"]
        assert case["maximum"] == cube_size * max(case["top"]), (n, case["name"])
        # Mixing parities of successive optimal sizes gives the claimed linear
        # envelope exactly. Check all cost grid points of denominator 2^n.
        kmax = case["first_max"]
        for cnum in range(n * cube_size + 1):
            if cnum >= kmax * cube_size:
                mix_score = Fraction(case["top"][kmax], den)
                mix_cost = Fraction(kmax)
            else:
                j, r = divmod(cnum, cube_size)
                prob = Fraction(r, cube_size)
                mix_score = ((1 - prob) * Fraction(case["top"][j], den)
                             + prob * Fraction(case["top"][j + 1], den))
                mix_cost = (1 - prob) * j + prob * (j + 1)
            assert mix_cost <= Fraction(cnum, cube_size)
            assert mix_score >= 0
        slack = case["minimum_positive_slack"]
        out_cases.append({
            "name": case["name"],
            "probabilities": [rational(p) for p in case["p"]],
            "eta": rational(case["eta"]),
            "parity_scores_by_size": [rational(Fraction(w, den)) for w in case["top"]],
            "first_maximizing_size": kmax,
            "exhaustive_maximum_score": rational(Fraction(case["maximum"], cube_size * den)),
            "number_of_maximizing_truth_tables": case["maximizers"],
            "number_attaining_budget_envelope_at_own_minimum_tree_cost": case["budget_equalities"],
            "minimum_positive_budget_slack": None if slack is None else rational(Fraction(slack, cube_size * den)),
            "truth_tables_checked": rules,
            "randomized_parity_mixture_cost_grid_points_checked": n * cube_size + 1,
            "direct_transition_equals_fourier": True,
            "closed_spectral_formula_verified": True,
            "unrestricted_maximum_verified": True,
            "budget_inequality_verified": True,
        })
    distribution = Counter(costs)
    return {
        "dimension": n,
        "truth_tables": rules,
        "minimum_expected_tree_cost_distribution": {
            rational(Fraction(k, cube_size)): distribution[k] for k in sorted(distribution)},
        "number_with_influence_equal_to_minimum_expected_tree_cost": influence_tree_equalities,
        "cases": out_cases,
    }


def finite_example(p: list[Fraction], eta: Fraction) -> dict:
    a = 1 - 2 * eta
    cumulative = Fraction(0)
    w = [Fraction(0)]
    for k, pk in enumerate(p, 1):
        cumulative += pk
        w.append((1 + a**k * (2*cumulative - 1)) / 2)
    return {"n": len(p), "eta": rational(eta),
            "first_maximizing_size": w.index(max(w)),
            "maximum_score": rational(max(w)),
            "parity_scores_by_size": [rational(x) for x in w]}


def crossover_examples() -> dict:
    uniform = []
    for n in [4, 8, 16, 32, 64]:
        for eta in [Fraction(1, 100), Fraction(1, 10), Fraction(1, 4), Fraction(1, 2)]:
            row = finite_example([Fraction(1, n)] * n, eta)
            # General discrete cutoff in the nondegenerate noise range:
            # first k with a*(2/n) <= (1-a)*(2*k/n - 1).
            a = 1 - 2 * eta
            if 0 < a < 1:
                threshold = Fraction(n, 2) + a / (1 - a)
                predicted = min(n, -((-threshold.numerator) // threshold.denominator))
                assert row["first_maximizing_size"] == predicted
            uniform.append(row)
    finite_geometric = []
    for n in [4, 8, 16, 32]:
        for eta in [Fraction(1, 100), Fraction(1, 10), Fraction(1, 4)]:
            finite_geometric.append(finite_example(
                [Fraction(2**(n - 1 - i), 2**n - 1) for i in range(n)], eta))
    infinite_geometric = []
    for ratio in [Fraction(1, 2), Fraction(2, 3), Fraction(9, 10)]:
        for eta in [Fraction(1, 100), Fraction(1, 10), Fraction(1, 4)]:
            a = 1 - 2 * eta
            cutoff = (1 - a) / (2 * (1 - a * ratio))
            k = 0
            while ratio**k > cutoff:
                k += 1
            scores = [Fraction(0)] + [
                (1 + a**j * (1 - 2*ratio**j)) / 2 for j in range(1, k + 5)]
            assert scores.index(max(scores)) == k
            infinite_geometric.append({
                "ratio": rational(ratio), "eta": rational(eta),
                "geometric_weights": "p_i=(1-r)*r^(i-1), i>=1",
                "cutoff_r_to_k": rational(cutoff),
                "first_maximizing_size": k,
                "maximum_score": rational(scores[k]),
                "nearby_parity_scores": [rational(x) for x in scores],
            })
    return {"finite_uniform": uniform,
            "finite_normalized_geometric": finite_geometric,
            "infinite_geometric": infinite_geometric}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    started = time.monotonic()
    costs = all_exact_tree_costs(args.max_n)
    dimensions = []
    for n in range(1, args.max_n + 1):
        dimensions.append(verify_dimension(n, costs[n]))
        print(f"n={n}: all {1 << (1 << n):,} Boolean functions, 8 rational cases: PASS", flush=True)
    document = {
        "description": "Exact exhaustive verification of noisy parity score and query-budget claims",
        "parameter_assumptions": "Uniform X; p_i nonincreasing, nonnegative, sum 1; 0<=eta<=1/2; same Boolean rule and shared randomness on both inputs",
        "arithmetic": "Integers and fractions.Fraction only",
        "decision_tree_cost": "Minimum expected number of adaptive bit queries to evaluate the rule exactly, under uniform input",
        "python_version": platform.python_version(),
        "total_distinct_truth_tables": sum(d["truth_tables"] for d in dimensions),
        "total_truth_table_parameter_pairs": sum(d["truth_tables"] * len(d["cases"]) for d in dimensions),
        "all_checks_passed": True,
        "dimensions": dimensions,
        "crossover_examples": crossover_examples(),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "scope": "Finite exhaustive checks support the algebra but do not establish infinite statements, a general proof, or historical novelty.",
    }
    args.output.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    print(f"Saved exact results to {args.output}", flush=True)


if __name__ == "__main__":
    main()
