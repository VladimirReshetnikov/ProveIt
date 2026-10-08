#!/usr/bin/env python3
"""Independent dense verification of the interval continuation rank threshold.

No fastunknot code is imported. Enumerate small complexes of dual-number
modules, including nonfree modules and unit differentials, then form the
actual total tensor differential as one binary matrix. This checks the
observation theorem without invoking a barcode or derived classification.
"""
from itertools import product
from pathlib import Path
import argparse
import json


def apply(columns, vector):
    answer = 0
    for j, column in enumerate(columns):
        if vector >> j & 1:
            answer ^= column
    return answer


def compose(left, right):
    return tuple(apply(left, column) for column in right)


def rank(columns):
    pivots = {}
    for column in columns:
        while column:
            pivot = column.bit_length() - 1
            if pivot in pivots:
                column ^= pivots[pivot]
            else:
                pivots[pivot] = column
                break
    return len(pivots)


def matrices(source, target):
    yield from product(range(1 << target), repeat=source)


def tensor_rank(length, dimensions, epsilon, arrows):
    offsets, count = {}, 0
    for i in range(length):
        for j, dimension in enumerate(dimensions):
            offsets[i, j] = count
            count += dimension
    differential = [0] * count
    for i in range(length):
        for j, dimension in enumerate(dimensions):
            for v in range(dimension):
                column = 0
                if i + 1 < length:
                    column ^= epsilon[j][v] << offsets[i + 1, j]
                if j + 1 < len(dimensions):
                    column ^= arrows[j][v] << offsets[i, j + 1]
                differential[offsets[i, j] + v] = column
    if any(apply(differential, column) for column in differential):
        raise AssertionError("constructed tensor differential does not square to zero")
    return count - 2 * rank(differential)


def enumerate_complexes(dimensions):
    endomorphisms = []
    for dimension in dimensions:
        zero = (0,) * dimension
        endomorphisms.append([e for e in matrices(dimension, dimension)
                             if compose(e, e) == zero])
    arrows = [list(matrices(dimensions[j], dimensions[j + 1]))
              for j in range(len(dimensions) - 1)]
    for epsilon in product(*endomorphisms):
        for differential in product(*arrows):
            if any(compose(epsilon[j + 1], d) != compose(d, epsilon[j])
                   for j, d in enumerate(differential)):
                continue
            if any(any(compose(differential[j + 1], differential[j]))
                   for j in range(len(differential) - 1)):
                continue
            yield epsilon, differential


def run():
    records = []
    total = checks = 0
    for dimensions in ((1,), (2,), (2, 1), (1, 2), (2, 2), (2, 2, 2)):
        cases = 0
        for epsilon, differential in enumerate_complexes(dimensions):
            ranks = [tensor_rank(length, dimensions, epsilon, differential)
                     for length in range(1, 7)]
            for length in range(1, 7):
                if min(3, ranks[length - 1]) != min(3, ranks[min(length, 3) - 1]):
                    raise AssertionError((dimensions, epsilon, differential, ranks))
                checks += 1
                if ranks[0] % 2 == 0:
                    if min(3, ranks[length - 1]) != min(3, ranks[min(length, 2) - 1]):
                        raise AssertionError((dimensions, epsilon, differential, ranks))
                    checks += 1
            cases += 1
        total += cases
        records.append({"dimensions": dimensions, "complexes": cases})
    # The simple module shows why cap2 is not universally safe; two copies
    # give the actual-closure parity class and show cap1 is not safe there.
    simple = [tensor_rank(l, (1,), ((0,),), ()) for l in range(1, 7)]
    even_simple = [tensor_rank(l, (2,), ((0, 0),), ()) for l in range(1, 7)]
    assert simple == list(range(1, 7))
    assert even_simple == list(range(2, 13, 2))
    return {"status": "passed", "complexes": total, "threshold_comparisons": checks,
            "maximum_interval_length": 6, "enumeration": records,
            "universal_cap2_counterexample_ranks": simple,
            "even_context_cap1_counterexample_ranks": even_simple,
            "implementation_imports": []}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    if arguments.output:
        arguments.output.write_text(text)
    print(text, end="")
