#!/usr/bin/env python3
"""Exact finite spectral-saturation classification, independent of Report295 code.

Only Python's standard library is used. All arithmetic deciding a branch,
candidate, tie, cutoff, or certificate is integer arithmetic. No floating-point
or radical approximations occur. The analytic input is documented in PROOF.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


MAXIMA = {
    3: 1, 4: 1, 5: 1, 6: 1, 7: 1, 8: 2, 9: 3, 10: 6,
    11: 53, 12: 4, 13: 2, 14: 1, 15: 1,
}


def require(condition: bool, message: str) -> None:
    """An invariant check that remains active under python -O."""
    if not condition:
        raise ValueError(message)


def W(n: int, m: int) -> int:
    """Polynomial comparator for the reflection branches (not their norm)."""
    return m * (n - m) * (n - 2 * m) ** 4


def less_than_npstar(n: int, m: int) -> bool:
    """Exact test m < n(1-sqrt(2/3))/2 for 0 <= m <= n/2."""
    require(0 <= 2 * m <= n, "invalid domain for exact pstar comparison")
    return 3 * (n - 2 * m) ** 2 > 2 * n * n


def candidates(n: int) -> list[int]:
    """Clipped floor and ceiling, found by an independent integer search."""
    require(n >= 3, "candidate reduction requires n >= 3")
    lo, hi = 0, n // 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if less_than_npstar(n, mid):
            lo = mid
        else:
            hi = mid - 1
    floor = lo  # npstar is irrational, so no exact-integer endpoint.
    clip = lambda x: max(1, min(n // 2, x))
    return sorted({clip(floor), clip(floor + 1)})


def exact_cutoff_checks() -> dict:
    """Rational inequalities establishing 1186 < 594+242 sqrt(6) < 1187."""
    checks = {
        # 1/11 < pstar < 1/10; pstar < 21/220.
        "pstar_above_1_over_11": 3 * 81 - 2 * 121,
        "pstar_below_1_over_10": 2 * 25 - 3 * 16,
        "pstar_below_midpoint": 2 * 110**2 - 3 * 89**2,
        "cutoff_above_1186": 6 * 242**2 - 592**2,
        "cutoff_below_1187": 593**2 - 6 * 242**2,
    }
    require(all(value > 0 for value in checks.values()), "cutoff inequality failed")
    return checks


def compact_certificate() -> dict:
    rows = []
    for q in range(3, 22):
        maximum = MAXIMA.get(q, 0)
        direction = -1 if q <= 10 else 1
        row = {"q": q, "last_winning_m": maximum, "neighbor_direction": direction}
        if maximum:
            n, m = q * maximum, maximum
            if m == 1 and direction == -1:
                row["last_winner"] = {"m": m, "reason": "smallest grid point to right of pstar"}
            else:
                gap = W(n, m) - W(n, m + direction)
                require(gap > 0, f"last-winner gap is not positive: q={q}, m={m}")
                row["last_winner"] = {"m": m, "n": n, "gap": gap}
        m = maximum + 1
        n = q * m
        require(1 <= m + direction <= n // 2, f"invalid competitor: q={q}, m={m}")
        gap = W(n, m) - W(n, m + direction)
        require(gap < 0, f"first-loser gap is not negative: q={q}, m={m}")
        row["first_loser"] = {"m": m, "n": n, "gap": gap}
        rows.append(row)
    return {
        "schema": "finite-saturation-compact-v1",
        "comparator": "W(n,m)=m*(n-m)*(n-2*m)^4",
        "positive_gap_means": "m beats its indicated adjacent competitor",
        "analytic_tail": "q>=22: (m+1)/(q*m)<=2/q<=1/11<pstar",
        "cutoff_checks": exact_cutoff_checks(),
        "rows": rows,
    }


def exhaustive_certificate() -> dict:
    """Compare EVERY allowed branch, rather than trusting a candidate reducer."""
    rows, saturating, ties = [], [], []
    for n in range(3, 1187):
        values = [(W(n, m), m) for m in range(1, n // 2 + 1)]
        best = max(v for v, m in values)
        winners = [m for v, m in values if v == best]
        if len(winners) != 1:
            ties.append({"n": n, "multiplicities": winners})
        candidate_set = candidates(n)
        require(set(winners) <= set(candidate_set), f"winner outside candidates: n={n}")
        candidate_values = [[m, W(n, m)] for m in candidate_set]
        losers = [(v, m) for v, m in values if v < best]
        runner_up = max(losers) if losers else None
        row = {
            "n": n,
            "winners": winners,
            "W": best,
            "candidate_values": candidate_values,
            "candidate_gap": abs(candidate_values[0][1] - candidate_values[-1][1])
                if len(candidate_values) == 2 else None,
            "runner_up_m": runner_up[1] if runner_up else None,
            "runner_up_W": runner_up[0] if runner_up else None,
            "gap_to_every_other_branch": best - runner_up[0] if runner_up else None,
        }
        if len(candidate_values) == 2:
            require(row["candidate_gap"] > 0, f"adjacent candidate tie: n={n}")
        if runner_up:
            require(row["gap_to_every_other_branch"] > 0, f"nonpositive winner gap: n={n}")
        rows.append(row)
        saturating.extend([n, m, n // m] for m in winners if n % m == 0)
    expected = sorted([q * m, m, q] for q, limit in MAXIMA.items() for m in range(1, limit + 1))
    require(not ties, f"unexpected maximizing ties: {ties}")
    require(saturating == expected, "exhaustive search differs from proposed classification")
    require(len(expected) == len({n for n, m, q in expected}) == 77, "wrong count or duplicate orders")
    require(max(n for n, m, q in expected) == 583, "wrong final saturation order")
    return {
        "schema": "finite-saturation-exhaustive-v1",
        "range": [3, 1186],
        "orders_checked": len(rows),
        "branches_checked": sum(n // 2 for n in range(3, 1187)),
        "ties": ties,
        "saturating": saturating,
        "rows": rows,
    }


def check_algebra_and_edges() -> None:
    """Integer polynomial identities and representative boundary regressions."""
    # The denominator rationalization has coefficients of 1 and s, s^2=3u.
    # (n-s)(n+2s)^2 = n^3 + 3(n^2-4u)s.
    for n in range(3, 130):
        for m in range(1, n // 2 + 1):
            u = m * (n - m)
            require(n * n - 4 * u == (n - 2 * m) ** 2, "square identity failed")
            require((3 * (n * n - 4 * u))**2 * (3 * u) == 27 * W(n, m), "comparator identity failed")
            # Exact comparison to the next branch has the stated factorization.
            if m + 1 <= n // 2:
                x, y = n - 2 * m, n - 2 * (m + 1)
                require(4 * (W(n, m) - W(n, m + 1)) == (
                    (x*x - y*y) * ((x*x + y*y) * n*n - (x**4 + x*x*y*y + y**4))
                ), "adjacent difference identity failed")
    require(candidates(3) == [1], "n=3 clipping regression")
    require(candidates(10) == [1], "n=10 clipping regression")
    require(candidates(11) == [1, 2], "n=11 candidate regression")
    require(W(583, 53) > W(583, 54), "last saturation boundary regression")
    require(W(594, 54) < W(594, 55), "first q=11 nonsaturation boundary regression")


def encode(obj: dict) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", type=Path, help="write deterministic certificates to this directory")
    mode.add_argument("--verify", type=Path, help="recompute and compare certificates in this directory")
    args = parser.parse_args()
    check_algebra_and_edges()
    results = {
        "compact_certificate.json": compact_certificate(),
        "finite_certificate.json": exhaustive_certificate(),
    }
    for name, obj in results.items():
        data = encode(obj)
        if args.write:
            args.write.mkdir(parents=True, exist_ok=True)
            (args.write / name).write_bytes(data)
        if args.verify:
            require((args.verify / name).read_bytes() == data, f"certificate differs: {name}")
        print(f"{name}: {len(data)} bytes; SHA256 {hashlib.sha256(data).hexdigest()}")
    full = results["finite_certificate.json"]
    print(f"PASS: {full['orders_checked']} orders, {full['branches_checked']} branches; no ties.")
    print("PASS: exactly 77 saturating orders >=3, largest 583; q-ranges independently certified.")
    print("PASS: exact clipped candidates, cutoff inequalities, polynomial identities, and boundary tests.")


if __name__ == "__main__":
    main()
