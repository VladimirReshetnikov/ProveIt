"""Independent finite checks for the adaptive nine-group mode contraction."""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import prod, sqrt, pi, log, log2
from pathlib import Path
import random

from adaptive_blocks import (
    PARTITIONS, adaptive_contract, crossing_edges, direct_contract,
    select_partition, validate_dimensions, streaming_contract, stream_path_pairs,
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    checks = Counter()
    edges = tuple((g, h) for g in range(9) for h in range(9) if g != h)
    inventory = {e: 1 for e in edges}
    require(len(PARTITIONS) == 280, "Wrong number of balanced partitions")
    require(len(set(PARTITIONS)) == 280, "Duplicate partitions")
    separated = Counter()
    for partition in PARTITIONS:
        require(sorted(v for b in partition for v in b) == list(range(9)), "Bad partition")
        require(all(len(b) == 3 for b in partition), "Bad block size")
        for e in crossing_edges(partition, inventory):
            separated[e] += 1
        for block in partition:
            vertices = set(block)
            incident = [e for e in edges if e[0] in vertices or e[1] in vertices]
            boundary = [e for e in edges if (e[0] in vertices) != (e[1] in vertices)]
            require(len(incident) == 42, "Bad block incident-pair count")
            require(len(boundary) == 36, "Bad boundary-pair count")
            checks["block_count_checks"] += 2
    for e in edges:
        require(separated[e] == 210, "Pair separation frequency is not 3/4")
        checks["separation_frequencies"] += 1

    rng = random.Random(20261027)
    for case in range(160):
        dims = {e: rng.randrange(1, 30) for e in edges}
        selected, cut = select_partition(dims)
        require(cut == prod(dims[e] for e in crossing_edges(selected, dims)), "Wrong cut product")
        require(cut ** 4 <= prod(dims.values()) ** 3, "Adaptive averaging inequality failed")
        require(all(cut <= prod(dims[e] for e in crossing_edges(p, dims)) for p in PARTITIONS),
                "Selected partition is not optimal")
        checks["exact_integer_averaging_cases"] += 1

    contraction_cases = []
    # Includes isolated groups, antiparallel indices, and nonuniform dimensions.
    fixtures = [{}, {(0, 1): 0}, {(0, 1): 2, (1, 0): 3},
                {(0, 1): 2, (1, 2): 2, (2, 0): 2},
                {(0, j): 2 for j in range(1, 9)}]
    for _ in range(55):
        selected_edges = rng.sample(edges, rng.randrange(1, 9))
        fixtures.append({e: rng.choice([1, 2, 2, 3]) for e in selected_edges})
    for case, dims in enumerate(fixtures):
        dims = validate_dimensions(dims)
        incidence = [tuple(e for e in dims if g in e) for g in range(9)]
        tables = []
        for g in range(9):
            tables.append({values: rng.randrange(-4, 5)
                           for values in product(*(range(dims[e]) for e in incidence[g]))})

        def factor(g, assignment):
            require(set(assignment) == set(incidence[g]), "Factor sees nonincident/missing indices")
            return tables[g][tuple(assignment[e] for e in incidence[g])]

        for modulus in [None, 2, 16, 257]:
            expected = direct_contract(dims, factor, modulus)
            actual, stats = adaptive_contract(dims, factor, modulus)
            require(actual == expected, "Adaptive contraction differs from literal sum")
            streamed, stream_stats = streaming_contract(dims, factor, modulus)
            require(streamed == expected, "Streaming binary contraction differs from literal sum")
            require(stream_stats["peak_assigned_indices"] <= stream_path_pairs(9),
                    "Streaming index stack exceeded its pair count")
            checks["streaming_contraction_comparisons"] += 1
            if all(dims.values()):
                wanted = sum(prod(dims[e] for e in incidence[g]) for g in range(9))
                require(stats["group_calls"] == wanted, "Incorrect number of cached group evaluations")
                require(stats["crossing_assignments"] == stats["crossing_domain_size"],
                        "Incorrect crossing enumeration length")
                checks["cache_call_checks"] += 1
            else:
                require(stats["group_calls"] == 0, "Empty domain should not evaluate any group")
                checks["empty_domain_checks"] += 1
            checks["exact_contraction_comparisons"] += 1
        contraction_cases.append({"case": case, "active_pair_count": len(dims),
                                  "literal_domain_size": prod(dims.values())})

    for bad in [{(0, 0): 2}, {(0, 9): 2}, {(0, 1): -1}, {(0, 1): 1.5},
                {(-1, 0): 2}, {(0, True): 2}, {"01": 2}]:
        try:
            validate_dimensions(bad)
        except ValueError:
            checks["negative_input_controls"] += 1
        else:
            raise RuntimeError("Invalid dimensions were accepted")

    for groups in [4, 8, 16, 32]:
        all_pairs = [(g,h) for g in range(groups) for h in range(groups) if g != h]
        for _ in range(5):
            active = rng.sample(all_pairs, 7)
            dims = {e: rng.choice([1, 2, 3]) for e in active}

            def generic_factor(g, assignment):
                require(set(assignment) == {e for e in dims if g in e},
                        "Generic streaming factor sees nonincident/missing indices")
                return ((g+1) + sum((e[0]+1)*(e[1]+2)*(v+1)
                                   for e,v in assignment.items())) % 11 - 5

            for modulus in [None, 2, 16]:
                expected = direct_contract(dims, generic_factor, modulus, groups)
                actual, stats = streaming_contract(dims, generic_factor, modulus, groups)
                require(actual == expected, "Generic streaming contraction mismatch")
                require(stats["peak_assigned_indices"] <= stream_path_pairs(groups),
                        "Generic streaming space bound failed")
                checks["generic_streaming_comparisons"] += 1

    # A comparison in which fixed-cut enumeration is particularly wasteful.
    fixed = PARTITIONS[0]
    fixed_cross = set(crossing_edges(fixed, inventory))
    dims = {e: 2 if e in fixed_cross else 1 for e in edges}
    selected, adaptive_size = select_partition(dims)
    fixed_size = prod(dims[e] for e in fixed_cross)
    require(adaptive_size < fixed_size, "Adversarial fixed-partition example did not improve")

    kappa = pi * sqrt(40 * log2(9)) / log(2)
    beta, cache, gamma, memory = sqrt(42) / 9, 4 / 9, 2 * sqrt(2) / 9, 2 / 3
    require(cache / (1 - gamma) < memory < beta, "Recursive cost hierarchy failed")
    require(1 / sqrt(2) < beta, "Adaptive triangle exceeds construction envelope")
    checks["coefficient_checks"] += 2
    log_lower = sum(Fraction(2, (2*j+1)*3**(2*j+1)) for j in range(4))
    require(log_lower > Fraction(6931, 10000), "Rational lower bound on ln(2) failed")
    require(9**5 < 2**16, "Rational upper bound on log2(9) failed")
    kappa_squared_upper = Fraction(22, 7)**2 * 128 / Fraction(6931, 10000)**2
    require(Fraction(42, 81) * kappa_squared_upper < 37**2, "Eventual time coefficient 37 not certified")
    require(Fraction(4, 9) * kappa_squared_upper < 35**2, "Eventual space coefficient 35 not certified")
    checks["exact_coefficient_certificates"] += 4
    low_gamma_squared = Fraction(200, 1377)
    require(low_gamma_squared < Fraction(31, 81)**2, "Low-degree recursive ratio certificate failed")
    require(Fraction(18, 25)**2 < Fraction(42, 81), "Low-degree cache comparison failed")
    require(162**5 < 2**37, "Low-degree logarithm upper bound failed")
    low_kappa_squared_upper = Fraction(22, 7)**2 * Fraction(740, 33) / Fraction(6931, 10000)**2
    require(Fraction(42, 81) * low_kappa_squared_upper < 16**2, "Low-degree time coefficient16 not certified")
    require(Fraction(4, 9) * low_kappa_squared_upper < 15**2, "Low-degree space coefficient15 not certified")
    low_kappa = pi * sqrt(100 * log2(162) / 33) / log(2)
    checks["exact_low_degree_certificates"] += 5
    require(stream_path_pairs(9) == 58 and stream_path_pairs(16) == 170,
            "Streaming recurrence mismatch")
    for exponent in range(1, 9):
        r = 2**exponent
        require(3*stream_path_pairs(r) == 2*(r*r-1), "Power-of-two streaming profile failed")
        checks["streaming_profile_checks"] += 1
    streaming_time = (5*pi*sqrt(17)/(2*log(2))) * (1+1/(3*sqrt(3)))
    require(Fraction(33,8)**2 > 17 and Fraction(12,7)**2 < 3,
            "Rational square-root brackets failed")
    streaming_upper = (Fraction(5)*Fraction(22,7)*Fraction(33,8)
                       /(2*Fraction(6931,10000)) * Fraction(43,36))
    require(streaming_upper < 56, "Eventual streaming coefficient56 not certified")
    checks["exact_streaming_coefficient_certificates"] += 2
    report = {
        "status": "PASS",
        "scope": "Finite mode-graph algebra and exact partition selection; not a SAT benchmark or asymptotic proof",
        "checks": dict(checks),
        "partition_count": len(PARTITIONS),
        "pairs": len(edges),
        "coefficients": {"kappa": kappa, "beta": beta, "cache_path": cache / (1 - gamma),
                         "time": kappa * beta, "space": kappa * memory,
                         "fixed_partition_strassen_same_schedule": kappa * sqrt(2 * (2 + (log2(7)-2)**2) / 9)},
        "low_degree_coefficients": {"time": low_kappa*beta, "space": low_kappa*memory,
                                    "cache_path": cache / (1 - sqrt(200/1377)),
                                    "scope": "Additional premise: root maximum degree at most ceil(s^(1/12))"},
        "polynomial_space_streaming": {"alphabet": 16, "path_pair_count": 170,
                                       "time_coefficient": streaming_time,
                                       "rational_upper": str(streaming_upper),
                                       "mode_enumeration_comparison_factor": sqrt(17/24)},
        "fixed_partition_example": {"fixed_partition": fixed, "chosen_partition": selected,
                                    "fixed_crossing_assignments": fixed_size,
                                    "adaptive_crossing_assignments": adaptive_size,
                                    "enumeration_reduction_factor": fixed_size // adaptive_size},
        "contraction_cases": contraction_cases,
    }
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
