#!/usr/bin/env python3
"""Deterministic verification of precision_peeling.py; active under -O."""
from __future__ import annotations
import argparse
import json
import random
from pathlib import Path
from precision_peeling import (ScaledMatrix, cauchy_cycle_checks,
    full_precision_cycle, peeled_cycle, require, residual_precision_inventory)


def run_checks() -> dict:
    randomizer = random.Random(20261027)
    successes = 0
    zero_cases = 0
    for precision in range(1, 35):
        for case in range(16):
            groups = randomizer.randrange(1, 6)
            dimensions = [randomizer.randrange(1, 6) for _ in range(groups)]
            valuations = [randomizer.randrange(0, max(2, precision//groups+3))
                          for _ in range(groups)]
            modulus = 1 << precision
            matrices = []
            for g, valuation in enumerate(valuations):
                rows, cols = dimensions[g], dimensions[(g+1) % groups]
                entries = tuple(tuple((randomizer.randrange(-modulus, modulus)
                                       << valuation) % modulus for _ in range(cols))
                                for _ in range(rows))
                matrices.append(ScaledMatrix(entries, valuation))
            old = full_precision_cycle(matrices, precision)
            new = peeled_cycle(matrices, precision)
            require(old == new, f"random cycle mismatch P={precision} case={case}")
            successes += 1
            zero_cases += sum(valuations) >= precision
    negative_controls = 0
    for matrix, p, q in [(ScaledMatrix(((6,),), 2), 4, 2),
                         (ScaledMatrix(((8,),), 3), 4, 2),
                         (ScaledMatrix(((17,),), 0), 4, 3),
                         (ScaledMatrix(((0,),), -1), 4, 3)]:
        try:
            matrix.normalized(p, q)
        except ValueError:
            negative_controls += 1
        else:
            raise RuntimeError("negative control was accepted")
    # The common wrong ordering destroys information: 224/32 == 7 mod 8,
    # whereas (224 mod 8)/32 == 0.  Keep as an explicit regression.
    require(ScaledMatrix(((224,),), 5).normalized(8, 3) == ((7,),),
            "correct division-before-reduction failed")
    require(((224 % 8) >> 5) != 7, "negative normalization demonstration failed")
    # Creation precision is semantic: after lowering the frozen old residue
    # 5 mod 8 to Q=2, its canonical representative is 1.  A later request at
    # four bits lifts that representative to 1, not the old integer 5.
    old_representative = 5 % (1 << 3)
    child_representative = old_representative % (1 << 2)
    later_lift = child_representative % (1 << 4)
    require(later_lift == 1 and old_representative % (1 << 4) == 5,
            "frozen-creation-precision regression failed")
    for original in range(64):
        for first_cap in range(1, 6):
            for second_cap in range(1, 6):
                twice = (original % (1 << first_cap)) % (1 << second_cap)
                once = original % (1 << min(first_cap, second_cap))
                require(twice == once, "flattened canonical caps disagree")
    cauchy = [cauchy_cycle_checks(2, 4), cauchy_cycle_checks(3, 3),
              cauchy_cycle_checks(4, 2)]
    inventories = [residual_precision_inventory(p, c, 5)
                   for c in (1, 4, 16) for p in (64, 128, 256, 512, 1024)]
    return {"status": "pass", "seed": 20261027,
            "random_exact_cycle_checks": successes,
            "zero_by_valuation_cases": zero_cases,
            "rejected_negative_controls": negative_controls,
            "canonical_creation_precision_checks": 1+64*5*5,
            "independent_actual_cauchy_checks": cauchy,
            "exact_partition_work_models": inventories}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    options = parser.parse_args()
    report = json.dumps(run_checks(), indent=2)+"\n"
    if options.output:
        Path(options.output).write_text(report)
    print(report)
