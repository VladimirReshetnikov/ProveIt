#!/usr/bin/env python3
"""Exact-arithmetic regression checks and theorem-based rational enclosures.

Python 3.10+; standard library only.  Run: python3 verify.py
Finite checks are not substituted for the all-parameter proofs in article.pdf.
The enclosures follow from those proofs; no numerical zeta oracle is used.
"""
from __future__ import annotations

import csv
import json
import random
from fractions import Fraction as Q
from functools import lru_cache
from math import comb
from pathlib import Path

OUT = Path(__file__).resolve().parent
COUNTS: dict[str, int] = {}


def require(condition: bool, category: str, detail: object = "") -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] = COUNTS.get(category, 0) + 1


def check_indices(n: int, m: int) -> None:
    if not isinstance(n, int) or not isinstance(m, int) or min(n, m) < 0:
        raise ValueError("Array indices must be nonnegative integers")


@lru_cache(maxsize=None)
def U(n: int, m: int) -> int:
    """A108625 as a square array, not its flattened antidiagonal indexing."""
    check_indices(n, m)
    return sum(comb(n, j) * comb(n + j, j) * comb(m, j)
               for j in range(min(n, m) + 1))


@lru_cache(maxsize=None)
def T(n: int, m: int) -> int:
    """A143007 as a square array."""
    check_indices(n, m)
    return sum(comb(n, j) * comb(n + j, j) * comb(m, j) * comb(m + j, j)
               for j in range(min(n, m) + 1))


def H(n: int, power: int) -> Q:
    return sum((Q(1, j ** power) for j in range(1, n + 1)), Q())


def E(n: int) -> Q:
    return sum((Q((-1) ** (j + 1), j * j) for j in range(1, n + 1)), Q())


def F2(n: int, m: int) -> Q:
    check_indices(n, m)
    return 2 * E(n) + (-1) ** n * sum(
        (Q(1, j * j * U(n, j - 1) * U(n, j)) for j in range(1, m + 1)), Q())


def F3(n: int, m: int) -> Q:
    check_indices(n, m)
    return H(n, 3) + sum(
        (Q(1, j ** 3 * T(n, j - 1) * T(n, j)) for j in range(1, m + 1)), Q())


def f3(n: int, m: int) -> int:
    return (n + m) * (n * n + n * m + m * m)


def edge(power: int, n: int, m: int, direction: str) -> Q:
    """Weight of edge ending at (n,m); direction is 'E' or 'N'."""
    if direction not in ("E", "N"):
        raise ValueError("Unknown direction")
    if power == 3:
        if direction == "E":
            return Q(1, n ** 3 * T(n - 1, m) * T(n, m))
        return Q(1, m ** 3 * T(n, m - 1) * T(n, m))
    if power == 2:
        if direction == "E":
            return Q(2 * (-1) ** (n + 1), n * n * U(n - 1, m) * U(n, m))
        return Q((-1) ** n, m * m * U(n, m - 1) * U(n, m))
    raise ValueError("Power must be 2 or 3")


def delta3(n: int, k: int) -> Q:
    m = n + k
    return Q(f3(n, m), n ** 3 * m ** 3 * T(n - 1, m - 1) * T(n, m))


def delta2(n: int, k: int, sub: bool = False) -> Q:
    x, y = (n + k, n) if sub else (n, n + k)
    f = x * x + 2 * x * y + 2 * y * y
    return Q((-1) ** (x + 1) * f,
             x * x * y * y * U(x - 1, y - 1) * U(x, y))


def bounds(power: int, n: int, m: int) -> tuple[Q, Q]:
    """Closed rational interval containing zeta(power), by the article."""
    if power == 3:
        M = max(n, m)
        if M < 1:
            raise ValueError("A nonzero coordinate is required")
        p = F3(n, m)
        b = Q(1, 2 * M * M * T(n, m) ** 2)
        return p, p + b
    if power == 2:
        p = F2(n, m)
        b = Q(2, (n + 1) ** 2 * U(n, m) * U(n + 1, m))
        if m > 0:
            b = min(b, Q(1, m * U(n, m) ** 2))
        return (p, p + b) if n % 2 == 0 else (p - b, p)
    raise ValueError("Power must be 2 or 3")


def decimal_floor(q: Q, digits: int) -> str:
    if q < 0:
        raise ValueError("This display routine expects nonnegative numbers")
    scaled = q.numerator * 10 ** digits // q.denominator
    return f"{scaled // 10 ** digits}.{scaled % 10 ** digits:0{digits}d}"


def common_digits(lo: Q, hi: Q, maximum: int = 350) -> tuple[int, str]:
    """Largest tested count d with floor(10^d lo)=floor(10^d hi)."""
    last = 0
    for d in range(1, maximum + 1):
        scale = 10 ** d
        if lo.numerator * scale // lo.denominator != hi.numerator * scale // hi.denominator:
            break
        last = d
    return last, decimal_floor(lo, last)


def width_exponent(width: Q) -> int:
    """Largest d in 0..999 for which width < 10^(-d)."""
    d = 0
    while d < 999 and width.numerator * 10 ** (d + 1) < width.denominator:
        d += 1
    return d


def exact_checks() -> None:
    # Every explicitly displayed rational approximant in the article.
    for n, target in enumerate((Q(6, 5), Q(351, 292), Q(62531, 52020)), 1):
        require(F3(n, n) == target, "displayed cubic example", n)
    for n, target in enumerate((Q(5, 3), Q(125, 76), Q(8705, 5292)), 1):
        require(F2(n, n) == target, "displayed quadratic example", n)
    require(F3(1, 2) == Q(125, 104), "displayed shifted example", "cubic")
    require(F2(1, 2) == Q(33, 20), "displayed shifted example", "super")
    require(F2(2, 1) == Q(23, 14), "displayed shifted example", "sub")
    # Two different finite binomial expressions for each OEIS array.
    for n in range(25):
        for m in range(25):
            alt_u = sum(comb(n, j) ** 2 * comb(n + m - j, m - j)
                        for j in range(min(n, m) + 1))
            alt_t = sum(comb(n, j) ** 2 * comb(n + m - j, m - j) ** 2
                        for j in range(min(n, m) + 1))
            require(U(n, m) == alt_u, "alternate U definition", (n, m))
            require(T(n, m) == alt_t, "alternate T definition", (n, m))
    for n in range(49):
        for m in range(49):
            require(T(n, m) == T(m, n), "T symmetry", (n, m))
            require(T(n + 1, m) >= T(n, m) and T(n, m + 1) >= T(n, m),
                    "T monotonicity", (n, m))
            require(U(n + 1, m) >= U(n, m) and U(n, m + 1) >= U(n, m),
                    "U monotonicity", (n, m))
            if n == 0 or m == 0:
                require(U(n, m) == T(n, m) == 1, "axis values", (n, m))
                continue
            A, B, C, D = T(n - 1, m - 1), T(n - 1, m), T(n, m - 1), T(n, m)
            f = f3(n, m)
            require(f * B == n ** 3 * D + m ** 3 * A, "T contiguity B", (n, m))
            require(f * C == m ** 3 * D + n ** 3 * A, "T contiguity C", (n, m))
            A, B, C, D = U(n - 1, m - 1), U(n - 1, m), U(n, m - 1), U(n, m)
            f = n * n + 2 * n * m + 2 * m * m
            require(f * B == n * n * D + 2 * m * m * A, "U contiguity B", (n, m))
            require(f * C == 2 * m * m * D - n * n * A, "U contiguity C", (n, m))
            if max(n, m) <= 24:
                for power in (2, 3):
                    require(edge(power, n, m - 1, "E") + edge(power, n, m, "N") ==
                            edge(power, n - 1, m, "N") + edge(power, n, m, "E"),
                            f"closed square zeta{power}", (n, m))
    # Certificates tested term by term, including the terminating endpoint.
    for n in range(1, 17):
        for m in range(1, 17):
            q = min(n, m)
            w = [Q(j ** 4 * comb(n, j) * comb(n + j, j) * comb(m, j) * comb(m + j, j),
                   (n + j) * (m + j)) for j in range(q + 1)] + [Q()]
            v = [Q(j ** 3 * comb(n, j) * comb(n + j, j) * comb(m, j), n + j)
                 for j in range(q + 1)] + [Q()]
            for j in range(q + 1):
                c = comb(n, j) * comb(n + j, j) * comb(m, j) * comb(m + j, j)
                d = comb(n, j) * comb(n + j, j) * comb(m, j)
                require(w[j + 1] - w[j] ==
                        Q((n * n * m * m - (n * n + m * m) * j * j) * c,
                          (n + j) * (m + j)), "W telescoper", (n, m, j))
                require(v[j + 1] - v[j] ==
                        Q((m * n * n - n * n * j - m * j * j) * d, n + j),
                        "V telescoper", (n, m, j))
    for k in range(16):
        s3, s2, s2sub = H(k, 3), H(k, 2), 2 * E(k)
        for n in range(1, 31):
            s3 += delta3(n, k)
            s2 += delta2(n, k)
            s2sub += delta2(n, k, True)
            require(s3 == F3(n, n + k), "finite zeta3 diagonal", (n, k))
            require(s2 == F2(n, n + k), "finite zeta2 superdiagonal", (n, k))
            require(s2sub == F2(n + k, n), "finite zeta2 subdiagonal", (n, k))
    rng = random.Random(20260920)
    for trial in range(300):
        n, m = rng.randrange(16), rng.randrange(16)
        path = ["E"] * n + ["N"] * m
        rng.shuffle(path)
        for power in (2, 3):
            x = y = 0
            total = Q()
            for step in path:
                if step == "E":
                    x += 1
                else:
                    y += 1
                total += edge(power, x, y, step)
            require(total == (F3(n, m) if power == 3 else F2(n, m)),
                    f"random path zeta{power}", (trial, n, m))
    for n in range(1, 41):
        for m in range(21):
            require((n + 1) ** 3 * T(n + 1, m) ==
                    (2 * n + 1) * (n * n + n + 2 * m * m + 2 * m + 1) * T(n, m)
                    - n ** 3 * T(n - 1, m), "T row recurrence", (n, m))
        for k in range(11):
            m = n + k
            fn, fn1 = f3(n, m), f3(n + 1, m + 1)
            pn, pn1 = n ** 3 * m ** 3, (n + 1) ** 3 * (m + 1) ** 3
            hn = (2 * n + 1) * (n * n + n + 2 * m * m + 2 * m + 1)
            coefficient = fn1 * (fn * hn - n ** 6) - fn * (n + 1) ** 6
            require(pn1 * fn * T(n + 1, m + 1) ==
                    coefficient * T(n, m) - fn1 * pn * T(n - 1, m - 1),
                    "shifted T recurrence", (n, k))
            if n <= 15 and k <= 4:
                r0 = T(n - 1, m - 1) * F3(n - 1, m - 1)
                r1 = T(n, m) * F3(n, m)
                r2 = T(n + 1, m + 1) * F3(n + 1, m + 1)
                require(pn1 * fn * r2 == coefficient * r1 - fn1 * pn * r0,
                        "shifted companion recurrence", (n, k))


def write_certificates() -> list[str]:
    records = []
    summaries = []
    for family in ("zeta3", "zeta2-super", "zeta2-sub"):
        for k in (0, 1, 3, 10):
            N = 60
            n, m = (N + k, N) if family == "zeta2-sub" else (N, N + k)
            power = 3 if family == "zeta3" else 2
            lo, hi = bounds(power, n, m)
            digits, text = common_digits(lo, hi)
            require(lo < hi and digits >= 120, "certificate width", (family, k, digits))
            records.append({"family": family, "N": N, "k": k, "n": n, "m": m,
                            "lower": {"numerator": str(lo.numerator), "denominator": str(lo.denominator)},
                            "upper": {"numerator": str(hi.numerator), "denominator": str(hi.denominator)},
                            "certified_decimal_places": digits, "common_decimal_prefix": text,
                            "derivation": "The rational enclosure theorem in article.pdf; no zeta oracle."})
            summaries.append(f"{family:12s} k={k:2d}, N={N}: {digits} certified decimal places")
    for power in (2, 3):
        rows = [r for r in records if r["family"].startswith(f"zeta{power}")]
        lows = [Q(int(r["lower"]["numerator"]), int(r["lower"]["denominator"])) for r in rows]
        highs = [Q(int(r["upper"]["numerator"]), int(r["upper"]["denominator"])) for r in rows]
        require(max(lows) < min(highs), "independent interval intersection", power)
    (OUT / "certificates.json").write_text(json.dumps(records, indent=2) + "\n")
    with (OUT / "convergence_table.csv").open("w", newline="") as fp:
        writer = csv.writer(fp)
        writer.writerow(["family", "N", "k", "width_less_than_10_to_minus_d", "certified_decimal_places"])
        for family in ("zeta3", "zeta2-super", "zeta2-sub"):
            for N in (5, 10, 20, 40, 60):
                for k in (0, 1, 3):
                    n, m = (N + k, N) if family == "zeta2-sub" else (N, N + k)
                    lo, hi = bounds(3 if family == "zeta3" else 2, n, m)
                    digits, _ = common_digits(lo, hi)
                    writer.writerow([family, N, k, width_exponent(hi - lo), digits])
    with (OUT / "array_sample.csv").open("w", newline="") as fp:
        writer = csv.writer(fp)
        writer.writerow(["n", "m", "U_A108625", "T_A143007"])
        for n in range(11):
            for m in range(11):
                writer.writerow([n, m, U(n, m), T(n, m)])
    return summaries


def main() -> None:
    exact_checks()
    summaries = write_certificates()
    lines = ["EXACT-ARITHMETIC VERIFICATION REPORT", "Date: 2026-09-20", "",
             "Every check below passed. These finite checks supplement the written proof.",
             "Python standard library only; exact integers and fractions; no zeta oracle.", ""]
    lines.extend(f"{key}: {value}" for key, value in COUNTS.items())
    lines += [f"TOTAL CHECKS: {sum(COUNTS.values())}", "", "RATIONAL ENCLOSURES (N = 60)"]
    lines.extend(summaries)
    lines += ["", "Full exact endpoints: certificates.json", "PASS"]
    text = "\n".join(lines) + "\n"
    (OUT / "verification_report.txt").write_text(text)
    print(text)


if __name__ == "__main__":
    main()
