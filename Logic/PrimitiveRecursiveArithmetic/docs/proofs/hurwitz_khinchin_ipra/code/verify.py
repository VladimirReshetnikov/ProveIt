"""Run reproducible finite checks with: python3 code/verify.py.

Finite experiments support the arithmetic implementation.  They do not replace
proof, certify iPRA derivations, or execute the general Khintchine construction.
"""
import json
from fractions import Fraction as F
from math import gcd
from pathlib import Path
from random import Random
from finite_core import (convergents, denominator_pair, sqrt_name, phi_name,
    hurwitz_certificate, open_components, union_length, residual_closed_gaps,
    intersection_length, approximation_intervals, local_block)


def cell_length(intervals):
    """Independent endpoint-cell computation, without merging intervals."""
    endpoints = sorted({F(0), F(1)} | {x for z in intervals for x in z[:2] if 0 < x < 1})
    total = F(0)
    for a, b in zip(endpoints, endpoints[1:]):
        middle = (a + b) / 2
        if any(z[0] < middle < z[1] for z in intervals):
            total += b - a
    return total


def json_value(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: json_value(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_value(v) for v in value]
    return value


def run():
    report = {"status": "passed", "arithmetic": "exact integers and fractions",
              "scope": "Finite checks only; no full cutoff or iPRA proof executed."}
    triples = 0
    for u in range(1, 81):
        for v in range(u, 81):
            if gcd(u, v) != 1:
                continue
            for a in range(1, 6):
                w = a * v + u
                j = denominator_pair(u, v, w)
                r, s = ((u, v), (v, w))[j]
                C = F(r * s, r * r + s * s)
                d = 1 - 5 * C * C
                assert d > 0 and 5 * (C + d / 50) ** 2 < 1
                triples += 1
    report["denominator_triples"] = triples

    examples = []
    for B in (0, 10, 100):
        for name, f, digits in (("phi", phi_name, [1] * (B + 4)),
                ("sqrt2", lambda s: sqrt_name(2, s), [1] + [2] * (B + 3))):
            cs = convergents(digits)
            for j in range(1, len(cs)):
                p, q = cs[j]
                r, s = cs[j - 1]
                assert abs(p * s - r * q) == 1 and q >= j
            examples.append({"name": name, **hurwitz_certificate(f, digits, B)})
    report["hurwitz_examples"] = examples

    touching = [(F(0), F(1, 2)), (F(1, 2), F(1))]
    assert open_components(touching) == touching
    assert residual_closed_gaps(touching) == [(F(0), F(0)), (F(1, 2), F(1, 2)), (F(1), F(1))]
    assert union_length([(F(1, 3), F(1, 3))]) == 0
    assert residual_closed_gaps([]) == [(F(0), F(1))]
    assert not approximation_intervals(lambda q: F(0), 1, 8)
    rng = Random(20261115)
    for _ in range(1000):
        intervals = []
        for _ in range(rng.randrange(25)):
            x, y = (F(rng.randrange(-10, 31), rng.randrange(1, 21)) for _ in range(2))
            intervals.append((min(x, y), max(x, y)))
        length = union_length(intervals)
        assert length == cell_length(intervals)
        split = len(intervals) // 2
        pairwise = [(max(a[0], b[0]), min(a[1], b[1]))
                    for a in intervals[:split] for b in intervals[split:]
                    if max(a[0], b[0]) < min(a[1], b[1])]
        assert intersection_length(intervals[:split], intervals[split:]) == cell_length(pairwise)
        assert length + sum((b - a for a, b in residual_closed_gaps(intervals)), F(0)) == 1
    report["random_union_cases"] = 1000
    report["random_intersection_cases"] = 1000
    report["edge_cases"] = ["zero radius", "touching singleton", "empty union", "conservative boundary singletons"]

    for case in range(1000):
        values = ([F(rng.randrange(31), 100) for _ in range(rng.randrange(25))]
                  if case % 2 else
                  [F(rng.randrange(501), rng.randrange(1, 101)) for _ in range(rng.randrange(25))])
        assert sum((min(x, F(1)) for x in values), F(0)) >= min(sum(values, F(0)), F(1))
    report["dyadic_cap_cases"] = 1000

    patterns = {"1/q": lambda q: F(1, q), "1/(4q)": lambda q: F(1, 4 * q),
                "1/q^2": lambda q: F(1, q * q), "1/10": lambda q: F(1, 10),
                "zero": lambda q: F(0)}
    counts, overlaps = [], 0
    for J in ((F(0), F(1)), (F(1, 4), F(3, 4)), (F(1, 7), F(6, 7))):
        L = J[1] - J[0]
        for pattern, psi in patterns.items():
            blocks = [local_block(J, k, psi) for k in range(3, 7)]
            for block in blocks:
                k, Q, t, radius = (block[z] for z in ("k", "Q", "t", "radius"))
                m = len(block["centers"])
                assert m >= 3 * L * Q * Q / 64 - 3 * Q * (k + 1)
                assert m <= L * Q * Q / 2 + 1
                assert m <= L * Q * Q and m >= L * Q * Q / 32
                assert union_length(block["intervals"]) == 2 * radius * m
                if pattern == "1/q":
                    counts.append({"J": J, "k": k, "centers": m})
            for i, left in enumerate(blocks):
                for right in blocks[i + 1:]:
                    actual = intersection_length(left["intervals"], right["intervals"])
                    exact_m_bound = right["t"] * union_length(left["intervals"]) / 4 + F(5, 4) * len(left["centers"]) * 2 * right["radius"]
                    k9 = L * left["t"] * right["t"] / 16 + F(5, 16) * L * F(4) ** (left["k"] - right["k"]) * right["t"]
                    assert actual <= exact_m_bound and actual <= k9
                    overlaps += 1
    report["local_count_cases"] = counts
    report["overlap_cases"] = overlaps
    report["local_count_scope"] = "Moderate samples satisfy K3 directly; the conservative general K4 threshold was not run."

    certificates = []
    for label in ("1/q", "1/(4q)", "1/q^2"):
        intervals = approximation_intervals(patterns[label], 5, 80)
        covered = union_length(intervals)
        gaps = residual_closed_gaps(intervals)
        assert covered + sum((b - a for a, b in gaps), F(0)) == 1
        assert all(gcd(z[2], z[3]) == 1 for z in intervals)
        if label == "1/q^2":
            assert covered <= 2 * sum((patterns[label](q) for q in range(5, 81)), F(0))
        certificates.append({"psi": label, "N": 5, "M": 80, "intervals": len(intervals),
            "covered_length": covered, "residual_length": 1 - covered,
            "residual_gaps": len(gaps), "singleton_gaps": sum(a == b for a, b in gaps)})
    report["finite_approximation_samples"] = certificates
    return report


if __name__ == "__main__":
    result = json_value(run())
    output = Path(__file__).with_name("verification.json")
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    summary = {key: result[key] for key in ("status", "denominator_triples", "random_union_cases", "dyadic_cap_cases", "overlap_cases")}
    print(json.dumps(summary, indent=2))
    print("Wrote", output)
