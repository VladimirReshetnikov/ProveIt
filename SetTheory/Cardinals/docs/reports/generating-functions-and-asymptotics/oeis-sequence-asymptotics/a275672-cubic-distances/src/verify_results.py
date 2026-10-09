#!/usr/bin/env python3
"""Independent checks of coordinates, arithmetic bounds, and case coverage.

This verifies witnesses and the completeness of the logged diameter split.
It does not replace rerunning or auditing the C++ impossibility search.
All mathematical assertions use exact integer or rational arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import json
import re

from finite_bounds import (
    KAPPA, exp_negative_interval, palette_and_parity_upper, palette_bits, row
)

ROOT = Path(__file__).resolve().parents[1]


def check_witness(record):
    n, points = record["n"], record["points"]
    assert record["size"] == len(points)
    assert len(set(map(tuple, points))) == len(points)
    assert all(len(p) == 3 for p in points)
    assert all(type(x) is int and 0 <= x < n for p in points for x in p)
    distances = [
        sum((x-y)**2 for x, y in zip(p, q))
        for p, q in combinations(points, 2)
    ]
    assert all(d > 0 for d in distances)
    assert len(set(distances)) == len(distances)
    assert sorted(distances) == record["squared_distances"]
    assert len(distances) == record["pair_count"]
    return len(distances)


def diameter_orbits(n, target):
    points = list(product(range(n), repeat=3))
    distances = sorted({
        x*x + y*y + z*z for x, y, z in points
    } - {0})
    threshold = distances[target*(target-1)//2-1]
    maps = []
    for perm in permutations(range(3)):
        for flip in product((False, True), repeat=3):
            maps.append([
                sum(
                    (n-1-p[perm[i]] if flip[i] else p[perm[i]]) * n**(2-i)
                    for i in range(3)
                ) for p in points
            ])
    cases = []
    eligible = 0
    for a, b in combinations(range(len(points)), 2):
        d = sum((points[a][i]-points[b][i])**2 for i in range(3))
        if d < threshold:
            continue
        eligible += 1
        representative = min(tuple(sorted((mp[a], mp[b]))) for mp in maps)
        if (a, b) == representative:
            cases.append((a, b, d))
    return eligible, cases


def check_case_coverage(path):
    certificate = json.loads(path.read_text())
    n = certificate["n"]
    target = certificate["target_ruled_out"]
    eligible, cases = diameter_orbits(n, target)
    source = ROOT / certificate["source_file"]
    assert hashlib.sha256(source.read_bytes()).hexdigest() == certificate["source_sha256"]
    pattern = re.compile(
        r"diameter_case (\d+) squared_distance (\d+) endpoints (\d+),(\d+) "
        r"result (\w+) nodes (\d+) seconds ([\d.]+)"
    )
    observed = []
    for line in (ROOT / certificate["log_file"]).read_text().splitlines():
        match = pattern.fullmatch(line)
        if not match:
            continue
        index, d, a, b, status, _, _ = match.groups()
        index = int(index)
        assert cases[index] == (int(a), int(b), int(d))
        assert status == "UNSAT"
        observed.append(index)
    assert observed == list(range(len(cases)))
    summary = certificate["summary"]
    assert summary["status"] == "UNSAT"
    assert summary["first_case"] == 0
    assert summary["last_case"] == len(cases)-1
    assert summary["case_count"] == len(cases)
    return {
        "n": n, "excluded_target": target, "eligible_edges": eligible,
        "covered_diameter_orbits": len(cases),
        "meaning": "Full case coverage checked; UNSAT relies on the audited C++ search."
    }


def check_kernel_independently():
    # This uses a different range reduction, Taylor order, and fixed-point
    # scale from verify_gaussian_certificate.py.
    nodes = (0, 3791, 6209, 10000)
    weights = (3183, 1817, 1817, 3183)
    intervals = [
        exp_negative_interval(F(10*d*d, 10**8))
        for d in range(10001)
    ]
    u = min(
        sum(
            F(w, 10000) * intervals[abs(i-p)][0]
            for p, w in zip(nodes, weights)
        )
        for i in range(5001)
    ) - F(1, 40000000)
    e = sum(
        F(v*w, 10**8) * intervals[abs(p-q)][1]
        for p, v in zip(nodes, weights) for q, w in zip(nodes, weights)
    )
    assert u >= F(36532567, 10**8)
    assert e <= F(36533029, 10**8)
    assert KAPPA == 2*F(36532567, 10**8)**3-F(36533029, 10**8)**3
    assert F(1, 6)/KAPPA < F(1849, 1000)**2
    return "Independent degree-31/30, seven-squaring rational check passed."


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for first in range(total+1):
            for rest in compositions(total-first, parts-1):
                yield (first,) + rest


def check_mod4_obstruction():
    capacities = (14, 17, 17, 8)
    tested = 0
    for occupancy in compositions(11, 8):
        tested += 1
        used = [sum(t*(t-1)//2 for t in occupancy), 0, 0, 0]
        for i in range(8):
            for j in range(i):
                used[(i^j).bit_count()] += occupancy[i]*occupancy[j]
        assert any(a > b for a, b in zip(used, capacities))
    assert tested == 31824
    return tested


def main():
    catalog = json.loads((ROOT/"data/witnesses.json").read_text())["witnesses"]
    pair_count = sum(check_witness(r) for r in catalog)
    assert [r["n"] for r in catalog] == list(range(31))
    for n in range(31):
        direct = {
            x*x+y*y+z*z for x, y, z in product(range(n), repeat=3)
        } - {0}
        bits = sum(1 << d for d in direct)
        assert bits == palette_bits(n)
        arithmetic = palette_and_parity_upper(n)
        assert arithmetic["distance_count"] == len(direct)
        assert arithmetic["odd_distances"] == sum(d % 2 for d in direct)
    certificates = sorted((ROOT/"data").glob("*_exact_certificate.json"))
    certificates += sorted((ROOT/"data").glob("*_upper_certificate.json"))
    coverage = [check_case_coverage(p) for p in certificates]
    kernel = check_kernel_independently()
    count = check_mod4_obstruction()
    partial = 2*sum((F(5, 7)**(2*j+1)/F(2*j+1) for j in range(10)), F(0))
    tail = 2*F(5, 7)**21/(21*(1-F(5, 7)**2))
    assert partial > F(179, 100) and partial+tail < F(9, 5)
    large = json.loads((ROOT/"data/large_n_upper_bounds.json").read_text())
    assert all(row(r["n"]) == r for r in large)
    result = {
        "status": "PASS",
        "witnesses_checked": len(catalog),
        "total_unordered_pairs_checked": pair_count,
        "palette_crosschecks": "Independent ordered-triple enumeration for n=0..30",
        "case_coverage_checks": coverage,
        "kernel_check": kernel,
        "mod4_occupancy_vectors_excluded": count,
        "analytic_logarithm_bracket": "179/100 < log(6) < 9/5",
        "finite_upper_bound_rows_recomputed": len(large),
        "limits": "Case records are not formal UNSAT proof traces; see article."
    }
    (ROOT/"data/verification_report.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
