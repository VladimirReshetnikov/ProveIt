#!/usr/bin/env python3
"""Exact independent certificate verifier; Python standard library only."""

from fractions import Fraction
import argparse
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run this certificate verifier without Python's -O option")


def expected_hyperplanes(kind, n):
    result = []
    for size in range(1, n + 1):
        for mask in range(1, 2 ** n):
            bits = [(mask // (2 ** i)) % 2 for i in range(n)]
            if sum(bits) != size:
                continue
            levels = range(1, size if kind == "C" else size + 1)
            for level in levels:
                result.append({"mask": mask, "level": level,
                               "normal": bits if kind == "C" else [1] + bits})
    return result


def exact_constraints(dimension, planes, signs):
    rows = []
    for coordinate in range(dimension):
        low = [0] * dimension
        low[coordinate] = -1
        rows.append((low, 0))
        high = [0] * dimension
        high[coordinate] = 1
        rows.append((high, 1))
    for index, bit in enumerate(signs):
        assert bit in "01"
        plane = planes[index]
        sign = 1 if bit == "0" else -1
        rows.append(([sign * a for a in plane["normal"]], sign * plane["level"]))
    return rows


def verify_case(case):
    kind, n = case["kind"], case["n"]
    assert kind in ("C", "D") and isinstance(n, int) and n >= 0
    dimension = n + (kind == "D")
    assert case["dimension"] == dimension
    planes = expected_hyperplanes(kind, n)
    assert case["hyperplanes"] == planes
    length = len(planes)
    pruned = {}
    for cert in case["pruned"]:
        prefix = cert["prefix"]
        assert prefix and 1 <= len(prefix) <= length and prefix not in pruned
        rows = exact_constraints(dimension, planes, prefix)
        y = [Fraction(0) for _ in rows]
        for index, value in cert["multipliers"]:
            assert isinstance(index, int) and 0 <= index < len(rows)
            assert y[index] == 0
            y[index] = Fraction(value)
            assert y[index] > 0
        assert sum(y) == 1
        for coordinate in range(dimension):
            assert sum(weight * row[0][coordinate]
                       for weight, row in zip(y, rows)) == 0
        upper_bound = sum(weight * row[1] for weight, row in zip(y, rows))
        assert upper_bound == Fraction(cert["upper_bound"]) and upper_bound <= 0
        pruned[prefix] = cert

    chambers = {}
    patterns = set()
    for cert in case["chambers"]:
        signs = cert["signs"]
        assert len(signs) == length and signs not in chambers
        point = [Fraction(v) for v in cert["point"]]
        margin = Fraction(cert["margin"])
        assert len(point) == dimension and margin > 0
        for coefficients, bound in exact_constraints(dimension, planes, signs):
            assert sum(a * v for a, v in zip(coefficients, point)) + margin <= bound
        offset = Fraction(0) if kind == "C" else point[0]
        slopes = point if kind == "C" else point[1:]
        values = []
        for mask in range(2 ** n):
            value = offset + sum(slopes[i] for i in range(n)
                                 if (mask // (2 ** i)) % 2)
            values.append(value.numerator // value.denominator)
        assert values == cert["carry_values"]
        assert tuple(values) not in patterns
        patterns.add(tuple(values))
        chambers[signs] = cert

    # This tree check is the completeness check. Every binary branch either
    # ends in a nonpositive-margin dual certificate or reaches a witnessed leaf.
    used_prunes, used_chambers = set(), set()
    layer_counts = [0] * (length + 1)

    def walk(prefix):
        if prefix in pruned:
            used_prunes.add(prefix)
            return
        layer_counts[len(prefix)] += 1
        if len(prefix) == length:
            assert prefix in chambers
            used_chambers.add(prefix)
            return
        walk(prefix + "0")
        walk(prefix + "1")

    walk("")
    assert used_prunes == set(pruned)
    assert used_chambers == set(chambers)
    assert layer_counts == case["layers"]
    assert case["count"] == len(chambers) == len(patterns)
    assert case["lp_calls"] == 2 * sum(layer_counts[:-1])
    return len(chambers), len(pruned)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("file", type=Path, nargs="?",
                        default=Path(__file__).with_name("carry_certificates.json"))
    args = parser.parse_args()
    data = json.loads(args.file.read_text())
    assert data["format"] == "carry-chamber-certificates-v1"
    seen = set()
    total_chambers = total_prunes = 0
    for case in data["cases"]:
        key = case["kind"], case["n"]
        assert key not in seen
        seen.add(key)
        chambers, prunes = verify_case(case)
        total_chambers += chambers
        total_prunes += prunes
        print(f"VERIFIED {key[0]}_{key[1]} = {chambers}: "
              f"{chambers} rational witnesses, {prunes} exact dual certificates")
    expected = {("C", n) for n in range(5)} | {("D", n) for n in range(4)}
    assert seen == expected
    print(f"ALL VERIFIED: {total_chambers} chambers and {total_prunes} pruned branches")


if __name__ == "__main__":
    main()
