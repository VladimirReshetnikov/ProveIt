"""Reproducible binary-size benchmarks; no expanded sheets are constructed.

Run: python agent_family/benchmark_affine_modular.py --output agent_family/benchmarks.json
These measure the arithmetic subproblem, not end-to-end unknot recognition.
"""

import argparse
import hashlib
import json
import platform
import random
from statistics import median
from time import perf_counter

from affine_modular import optimise_cyclic_affine_family


def fingerprint(integers):
    digest = hashlib.sha256()
    for value in integers:
        digest.update(hex(value).encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


def timed_family(arguments, expected, repetitions=3):
    elapsed = []
    result = None
    for _ in range(repetitions):
        start = perf_counter()
        result = optimise_cyclic_affine_family(*arguments)
        elapsed.append(perf_counter() - start)
        assert result["minimum_components"] == expected
    return result, elapsed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="benchmarks.json")
    options = parser.parse_args()
    records = []
    for exponent in (16, 64, 256, 1024, 4096, 16384, 65536):
        modulus = 6 ** exponent
        result, elapsed = timed_family((modulus, [2], [[1]]), 1)
        assert result["parameters"] == [3 ** exponent]
        records.append({
            "case": "prime_power_saturation",
            "input_formula": "m=6^e, h(z)=2+z, no seams",
            "exponent_e": exponent,
            "modulus_bits": modulus.bit_length(),
            "variables": 1,
            "constraints": 0,
            "holonomies": 1,
            "minimum_components": result["minimum_components"],
            "saturation_gcd_calls": result["saturation_gcd_calls"],
            "seconds": elapsed,
            "median_seconds": median(elapsed),
            "witness_sha256": fingerprint(result["parameters"]),
            "solution_count_bits": result["solution_count"].bit_length(),
        })

    for bits in (128, 512, 2048, 8192):
        modulus = 6 * ((1 << bits) + 1)
        randomizer = random.Random(20261008 + bits)
        variables, constraints, loops = 24, 12, 7
        matrix = [[randomizer.randrange(modulus) for _ in range(variables)]
                  for _ in range(constraints)]
        hidden = [6 * randomizer.randrange(modulus // 6) for _ in range(variables)]
        rhs = [sum(a * z for a, z in zip(row, hidden)) % modulus for row in matrix]
        holonomy = [[(matrix[index][j] + 6 * randomizer.randrange(modulus)) % modulus
                     for j in range(variables)] for index in range(loops - 1)]
        holonomy.append([0] * variables)
        constants = [0] * (loops - 1) + [6]
        result, elapsed = timed_family((modulus, constants, holonomy, matrix, rhs), 6)
        records.append({
            "case": "dense_constrained_affine_family",
            "input_formula": "m=6*(2^b+1), seeded dense A; H_j=A_j+6R_j; final h=6",
            "exponent_b": bits,
            "seed": 20261008 + bits,
            "modulus_bits": modulus.bit_length(),
            "variables": variables,
            "constraints": constraints,
            "holonomies": loops,
            "minimum_components": result["minimum_components"],
            "saturation_gcd_calls": result["saturation_gcd_calls"],
            "seconds": elapsed,
            "median_seconds": median(elapsed),
            "witness_sha256": fingerprint(result["parameters"]),
            "solution_count_bits": result["solution_count"].bit_length(),
            "nonzero_dual_entries": sum(value != 0 for row in result["dual_rows"]
                                        for value in row),
        })

    report = {
        "scope": "Affine modular optimizer including exact optimality-certificate generation and verification",
        "date": "2026-10-08",
        "python": platform.python_version(),
        "platform": platform.platform(),
        "repetitions_per_case": 3,
        "factorization_calls": 0,
        "expanded_sheet_records": 0,
        "enumerated_parameter_tuples": 0,
        "records": records,
    }
    with open(options.output, "w", encoding="utf-8") as handle:
        json.dump(report, handle, indent=2)
        handle.write("\n")
    for record in records:
        print(record["case"], record["modulus_bits"],
              f'{record["median_seconds"]:.6f}s',
              "minimum", record["minimum_components"])


if __name__ == "__main__":
    main()
