"""Rebuild small-stage data, a formula witness, and verification metadata.

Run from any directory: python code/reproduce.py
The largest enumerated stage is S_6. S_7 is cited, not recomputed.
"""
from __future__ import annotations
import csv
import gzip
import json
import math
import platform
import sys
from itertools import combinations_with_replacement
from pathlib import Path

from a352969 import (ExpressionBuilder, check_certificate,
                     counting_bound_parameters, maximum, reachable_cached)

BASE = Path(__file__).resolve().parent.parent


def prime_sieve(limit: int) -> bytearray:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            flags[p * p:limit + 1:p] = b"\x00" * ((limit - p * p) // p + 1)
    return flags


def main() -> None:
    data = BASE / "data"
    verification = BASE / "verification"
    data.mkdir(exist_ok=True)
    verification.mkdir(exist_ok=True)
    sets = [reachable_cached(n) for n in range(7)]
    rows = []
    for n, values in enumerate(sets):
        first_gap = 1
        while first_gap in values:
            first_gap += 1
        # A prime first appears at an addition node, hence p<=2*M_(n-1).
        prime_limit = 2 * maximum(n - 1) if n else 1
        sieve = prime_sieve(prime_limit)
        primes = [x for x in values if x <= prime_limit and sieve[x]]
        row = {"n": n, "a_n": len(values), "maximum": max(values),
               "initial_interval_end": first_gap - 1,
               "prime_count": len(primes), "largest_prime": max(primes, default=0),
               "normalized_log2": math.log2(len(values)) / (1 << n),
               "log2_log2_a_n": (math.log2(math.log2(len(values))) if n else ""),
               "input_pairs": 0, "candidate_values": 0,
               "sumset_size": 0, "productset_size": 0, "overlap": 0,
               "status": "independently computed"}
        if n:
            previous = sets[n - 1]
            sums = {x + y for x, y in combinations_with_replacement(previous, 2)}
            products = {x * y for x, y in combinations_with_replacement(previous, 2)}
            assert sums | products == values
            row.update(input_pairs=len(previous) * (len(previous) + 1) // 2,
                       candidate_values=len(previous) * (len(previous) + 1),
                       sumset_size=len(sums), productset_size=len(products),
                       overlap=len(sums & products))
        rows.append(row)
    reported = 357306081
    rows.append({"n": 7, "a_n": reported, "maximum": maximum(7),
                 "initial_interval_end": "", "prime_count": "", "largest_prime": "",
                 "normalized_log2": math.log2(reported) / 128,
                 "log2_log2_a_n": math.log2(math.log2(reported)),
                 "input_pairs": 67144 * 67145 // 2,
                 "candidate_values": 67144 * 67145,
                 "sumset_size": "", "productset_size": "", "overlap": "",
                 "status": "OEIS reported; not recomputed"})
    with (data / "sequence_statistics.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    with gzip.open(data / "sets_0_to_6.json.gz", "wt", encoding="utf-8") as f:
        json.dump({str(n): sorted(s) for n, s in enumerate(sets)}, f,
                  separators=(",", ":"))
    bounds = [counting_bound_parameters(n)
              for n in (16, 32, 64, 128, 256, 1024, 10000, 1000000)]
    with (data / "counting_bounds.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(bounds[0]))
        writer.writeheader()
        writer.writerows(bounds)
    value = int("d17c6b5309eaf42872bd0107c6935fa02e186cda95673bf08429ad3e7615c08f", 16)
    builder = ExpressionBuilder()
    root = builder.integer(value)
    certificate = builder.certificate(root)
    assert check_certificate(certificate)[0] == value
    (data / "expression_witness.json").write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    metadata = {"python_version": sys.version, "platform": platform.platform(),
                "max_enumerated_stage": 6, "reported_only_stage": 7,
                "value_indexed_oracle_limit_in_tests": 2000,
                "constructive_witness_bit_length": value.bit_length(),
                "constructive_witness_height": builder.heights[root],
                "constructive_witness_nodes": len(builder.nodes),
                "source": "https://oeis.org/A352969",
                "source_access_date": "2026-09-20",
                "note": "Finite tests are validation, not substitutes for the proofs."}
    (verification / "metadata.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    for row in rows:
        print(row)
    print("Witness:", metadata)


if __name__ == "__main__":
    main()
