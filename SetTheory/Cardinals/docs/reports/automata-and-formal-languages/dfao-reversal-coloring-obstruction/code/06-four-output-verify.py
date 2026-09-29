#!/usr/bin/env python3
"""Exact verification for the four-output reversal manuscript.

Standard library only. No assertions are used: checks remain active under -O.
The analytic proof handles n >= 26; the finite certificate covers 7 <= n <= 25.
The larger sweep is a regression check, not a substitute for the proof.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from collections import Counter
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd
from pathlib import Path
from typing import Iterator

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def split(n: int) -> tuple[int, int]:
    if n < 7:
        raise ValueError("The theorem and this split API require n >= 7.")
    h = n // 2
    if n % 2:
        return h, h + 1
    return (h - 1, h + 1) if h % 2 == 0 else (h - 2, h + 2)


def biclique(a: int, b: int) -> int:
    if a < 1 or b < 1:
        raise ValueError("Biclique parts must be positive.")
    return 6 * 2 ** (a + b) + 4 * (3 ** a + 3 ** b) - 12 * (2 ** a + 2 ** b) + 12


@lru_cache(maxsize=None)
def product_bound(r: int) -> int:
    if r < 0:
        raise ValueError("A residual size cannot be negative.")
    if r < 2:
        return 1
    q, t = divmod(r, 3)
    return 3 ** q if t == 0 else (4 * 3 ** (q - 1) if t == 1 else 2 * 3 ** q)


def deficit(n: int) -> int:
    a, b = split(n)
    return biclique(a, b) - a * b


def maximum(n: int) -> int:
    return 4 ** n - deficit(n)


def candidates(n: int) -> Iterator[tuple[int, tuple]]:
    """Every entry is a proved deficit lower bound for its structural case."""
    if n < 7:
        raise ValueError("Certificate range starts at n=7.")
    q, z = divmod(n, 4)
    balanced = factorial(n) // (factorial(q) ** (4 - z) * factorial(q + 1) ** z)
    yield 4 ** n - 3 ** n, ("nonsurjective",)
    yield 4 ** n - balanced, ("two_permutations",)
    yield 9 * 4 ** (n - 2) - 1, ("two_singular",)
    for m in range(2, n + 1):
        r = n - m
        for d in range(1, m):
            if m % d:
                continue
            length = m // d
            count = (3 ** length + (-1) ** length * 3) ** d * 4 ** r
            yield count - m * product_bound(r), ("cycle", m, d, r)
    for a in range(1, n):
        for b in range(a, n - a + 1):
            d, r = gcd(a, b), n - a - b
            count = biclique(a // d, b // d) ** d * 4 ** r
            yield count - (a * b // d) * product_bound(r), ("cross", a, b, d, r)


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def mobius(n: int) -> int:
    parity, p = 0, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            parity += 1
            if n % p == 0:
                return 0
        p += 1
    if n > 1:
        parity += 1
    return -1 if parity % 2 else 1


def primitive_surjections(colors: int, length: int) -> int:
    def surjections(d: int) -> int:
        return sum((-1) ** j * comb(colors, j) * (colors - j) ** d
                   for j in range(colors + 1))
    return sum(mobius(length // d) * surjections(d) for d in divisors(length))


def inventory(a: int, b: int) -> dict[tuple[int, int], int]:
    if gcd(a, b) != 1:
        raise ValueError("This inventory formula assumes coprime parts.")
    result = {}
    for u in divisors(a):
        for v in divisors(b):
            vertices = sum(
                factorial(4) // (factorial(i) * factorial(j) * factorial(4 - i - j))
                * primitive_surjections(i, u) * primitive_surjections(j, v)
                for i in range(1, 4) for j in range(1, 5 - i)
            )
            require(vertices % (u * v) == 0, "Nonintegral orbit inventory")
            result[u, v] = vertices // (u * v)
    return result


def word_period(word: tuple[int, ...]) -> int:
    n = len(word)
    return next(d for d in divisors(n)
                if all(word[i] == word[(i + d) % n] for i in range(n)))


def witness(n: int) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    a, b = split(n)
    p = tuple((q + 1) % a if q < a else a + (q - a + 1) % b for q in range(n))
    s = list(range(n))
    s[0], s[n - 1] = a, 0
    if a % 2:
        s[1], s[2] = s[2], s[1]
    tau = (0,) + (1,) * (a - 1) + (2,) + (3,) * (b - 1)
    return p, tuple(s), tau


def accessible(p: tuple[int, ...], s: tuple[int, ...]) -> bool:
    seen, queue = {0}, [0]
    for q in queue:
        for t in (p, s):
            if t[q] not in seen:
                seen.add(t[q])
                queue.append(t[q])
    return len(seen) == len(p)


def state_classes(p: tuple[int, ...], s: tuple[int, ...], tau: tuple[int, ...]) -> int:
    classes = tau
    while True:
        labels = {}
        refined = tuple(labels.setdefault((classes[q], classes[p[q]], classes[s[q]]), len(labels))
                        for q in range(len(p)))
        if len(set(refined)) == len(set(classes)):
            return len(set(refined))
        classes = refined


def multiply(a: list[int], b: list[int]) -> list[int]:
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def recurrence_polynomial() -> list[int]:
    """Ascending coefficients of (E-2)(E^4-9)(E^4-4)(E-1)^3(E+1)(E^2+1)."""
    factors = ([-2, 1], [-9, 0, 0, 0, 1], [-4, 0, 0, 0, 1],
               [-1, 1], [-1, 1], [-1, 1], [1, 1], [1, 0, 1])
    answer = [1]
    for factor in factors:
        answer = multiply(answer, factor)
    return answer


def residue_deficit(n: int) -> int:
    h = n // 2
    if n % 2:
        return 6 * 2 ** n + 16 * 3 ** h - 36 * 2 ** h + 12 - h * (h + 1)
    if h % 2 == 0:
        return 6 * 2 ** n + 40 * 3 ** (h - 1) - 60 * 2 ** (h - 1) + 13 - h * h
    return 6 * 2 ** n + 328 * 3 ** (h - 2) - 204 * 2 ** (h - 2) + 16 - h * h


def run(max_n: int) -> dict:
    if max_n < 25:
        raise ValueError("max_n must cover the entire finite proof range through 25.")
    out = ROOT / "data"
    out.mkdir(exist_ok=True)
    rows, total, base_total = [], 0, 0
    for n in range(7, max_n + 1):
        a, b = split(n)
        target = ("cross", a, b, 1, 0)
        entries = list(candidates(n))
        minimum = min(value for value, _ in entries)
        minimizers = [tag for value, tag in entries if value == minimum]
        require(minimum == deficit(n) and minimizers == [target], f"Structural comparison failed at {n}")
        runner, runner_tag = min((value, tag) for value, tag in entries if tag != target)
        row = dict(n=n, A=a, B=b, deficit=minimum, maximum=maximum(n),
                   margin=runner - minimum, candidates=len(entries),
                   runner_up=";".join(map(str, runner_tag)))
        rows.append(row)
        total += len(entries)
        if n <= 25:
            base_total += len(entries)
    for filename, selected in (("base_certificate.csv", rows[:19]), ("structural_sweep.csv", rows)):
        with (out / filename).open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(selected)

    # Independent descriptions of quantities in the theorem.
    for n in range(7, 1001):
        require(deficit(n) == residue_deficit(n), f"Residue formula failed at {n}")
        a, b = split(n)
        brute = min(((j, n-j) for j in range(1, n // 2 + 1) if gcd(j, n-j) == 1),
                    key=lambda pair: pair[1] - pair[0])
        require((a, b) == brute, f"Nearest split failed at {n}")
    require(40 * 3 ** 13 < 2 ** 26, "Threshold inequality failed")
    require(4 ** 14 - 3 ** 14 > 7 * 12 ** 7, "Cycle threshold failed")

    graph_cases, colorings_checked = 0, 0
    for a in range(1, 5):
        for b in range(a, 5):
            direct = sum(set(word[:a]).isdisjoint(word[a:])
                         for word in product(range(4), repeat=a+b))
            require(direct == biclique(a, b), f"Biclique count failed for {a,b}")
            graph_cases += 1
            colorings_checked += 4 ** (a+b)
    for length in range(2, 9):
        direct = sum(all(word[i] != word[(i+1) % length] for i in range(length))
                     for word in product(range(4), repeat=length))
        require(direct == 3 ** length + (-1) ** length * 3, f"Cycle count failed for {length}")
        graph_cases += 1
        colorings_checked += 4 ** length

    inventory_records = []
    for a, b in ((3, 4), (3, 5)):
        vertices: Counter = Counter()
        one_edge = 0
        for word in product(range(4), repeat=a+b):
            left, right = word[:a], word[a:]
            mono = sum(left.count(color) * right.count(color) for color in range(4))
            if mono == 0:
                vertices[word_period(left), word_period(right)] += 1
            elif mono == 1:
                one_edge += 1
        inv = inventory(a, b)
        for (u, v), count in inv.items():
            require(vertices[u,v] == u * v * count, f"Inventory failed for {a,b,u,v}")
        require(sum(vertices.values()) == biclique(a, b), "Inventory total failed")
        require(one_edge == 12 * a * b * (2 ** (a-1) + 2 ** (b-1) - 2), "Unique-edge penalty failed")
        inventory_records.append(dict(a=a, b=b, proper_colorings=sum(vertices.values()),
                                      unique_edge_colorings=one_edge,
                                      orbits=[dict(u=u, v=v, count=c) for (u,v), c in inv.items()]))

    for n in range(7, 201):
        p, s, tau = witness(n)
        require(accessible(p, s), f"Witness not accessible at {n}")
        require(state_classes(p, s, tau) == n, f"Witness not minimal at {n}")
        require(len(set(s)) == n - 1, f"Wrong singular rank at {n}")

    rec = recurrence_polynomial()
    degree = len(rec) - 1
    for n in range(7, 301):
        require(sum(c * deficit(n+j) for j, c in enumerate(rec)) == 0, f"Recurrence failed at {n}")
    denominator = rec[::-1]
    initial = [deficit(n) for n in range(7, 7 + degree)]
    numerator = [sum(denominator[j] * initial[i-j] for j in range(i+1)) for i in range(degree)]
    recurrence_record = dict(order=degree, advance_coefficients_ascending=rec,
                             tail_start=7, ogf_denominator_ascending=denominator,
                             ogf_numerator_ascending=numerator, initial_deficits=initial)
    (out / "recurrence.json").write_text(json.dumps(recurrence_record, indent=2) + "\n", encoding="utf-8")
    (out / "inventory.json").write_text(json.dumps(inventory_records, indent=2) + "\n", encoding="utf-8")
    report = dict(status="PASS", python=platform.python_version(),
                  finite_proof_range=[7,25], finite_proof_candidates=base_total,
                  regression_range=[7,max_n], regression_candidates=total,
                  unique_minimizer_in_every_case=True,
                  split_and_residue_checks=994,
                  direct_graph_cases=graph_cases, direct_graph_colorings=colorings_checked,
                  inventory_and_penalty_pairs=[[3,4],[3,5]],
                  inventory_colorings=4**7+4**8,
                  accessibility_and_minimality_range=[7,200],
                  recurrence_order=degree, recurrence_start_indices=[7,300],
                  assertion_independent=True)
    (out / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=200, help="Structural regression endpoint (at least 25)")
    args = parser.parse_args()
    print(json.dumps(run(args.max_n), indent=2))
