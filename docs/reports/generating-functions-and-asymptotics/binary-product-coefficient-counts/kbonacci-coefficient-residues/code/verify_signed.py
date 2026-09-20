"""Reproduce the signed-cancellation route's exact checks, tables, and large values.

Standard library only. This is the verification suite attached to the
signed-cancellation proof; its coverage table is reproduced in the article's
section on the two verification suites. The finite-state suite is
code/verify.py, and code/cross_check.py compares the two.

Do not run under `python -O`: the checks here are assertions.
"""
from __future__ import annotations
import csv
import itertools
import json
import platform
import random
import sys
import time
from decimal import Decimal, localcontext
from pathlib import Path
from math import prod
from kbonacci_parity import (
    CoefficientOracle, coherent_signs, count_fast, count_prefix,
    parity_bitset, signed_sparse, standard_seeds, weights,
)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def verify() -> dict:
    if not __debug__:
        raise RuntimeError("Verification requires assertions; do not use Python -O")
    rng = random.Random(20260919)
    report = {"python": platform.python_version(), "all_passed": False}
    start = time.perf_counter()
    bounds = []
    bitset_comparisons = 0
    for k in range(2, 26):
        a = weights(k, 40)
        expected = count_prefix(k, 40)
        bits, degree, last = 1, 0, 0
        assert expected[0] == bits.bit_count()
        bitset_comparisons += 1
        for n, w in enumerate(a, 1):
            if degree + w > 8_000_000:
                break
            degree += w
            bits ^= bits << w
            assert bits.bit_count() == expected[n], ("bitset", k, n)
            bitset_comparisons += 1
            last = n
        bounds.append({"k": k, "n_max": last, "degree": degree})
    report["direct_bitset"] = {"comparisons": bitset_comparisons, "bounds": bounds}

    # Dense integer multiplication does not use the count recurrence or oracle.
    dense_counts, coefficient_comparisons = 0, 0
    for k in range(2, 11):
        a = weights(k, 16)
        e = coherent_signs(k, 16)
        coeff = [1]
        expected = count_prefix(k, 16)
        for n, (w, s) in enumerate(zip(a, e), 1):
            new = [0] * (len(coeff) + w)
            for m, c in enumerate(coeff):
                new[m] += c
                new[m + w] += s * c
            coeff = new
            assert all(c in (-1, 0, 1) for c in coeff), ("flatness", k, n)
            assert sum(c*c for c in coeff) == expected[n]
            bits = parity_bitset(a[:n])
            oracle = CoefficientOracle(k, n)
            queries = set(range(min(100, len(coeff))))
            queries.update(rng.randrange(len(coeff)) for _ in range(100))
            queries.update([0, len(coeff)-1, w, sum(a[:n-1])])
            for m in queries:
                assert oracle.signed(m) == coeff[m], ("oracle", k, n, m)
                assert (bits >> m) & 1 == coeff[m]**2
                coefficient_comparisons += 1
            assert oracle.signed(-1) == oracle.signed(len(coeff)) == 0
            dense_counts += 1
    report["direct_signed_dense"] = {"k_min": 2, "k_max": 10, "n_max": 16,
                                      "products": dense_counts,
                                      "coefficient_queries": coefficient_comparisons}

    all_sign_cases = 0
    for k in range(2, 7):
        for seeds in (standard_seeds(k), [1 << i for i in range(k)]):
            a = weights(k, 12, seeds)
            for init in itertools.product((-1, 1), repeat=k):
                e = coherent_signs(k, 12, init)
                p = signed_sparse(a, e)
                assert all(abs(c) == 1 for c in p.values())
                assert len(p) == count_fast(k, 12)
                oracle = CoefficientOracle(k, 12, seeds, init)
                for m in rng.sample(range(sum(a)+1), min(40, sum(a)+1)):
                    assert oracle.signed(m) == p.get(m, 0)
                all_sign_cases += 1
    report["all_initial_signs"] = {"k_min": 2, "k_max": 6, "n": 12,
                                   "seed_families": 2, "cases": all_sign_cases}

    random_cases = 0
    for k in range(2, 10):
        for _ in range(12):
            seeds, total = [], 0
            for _ in range(k):
                value = total + rng.randrange(1, 8)
                seeds.append(value)
                total += value
            init = [rng.choice((-1, 1)) for _ in range(k)]
            a, e = weights(k, 12, seeds), coherent_signs(k, 12, init)
            p = signed_sparse(a, e)
            assert max(abs(c) for c in p.values()) == 1
            assert len(p) == count_prefix(k, 12)[-1]
            assert len(p) == parity_bitset(a).bit_count()
            oracle = CoefficientOracle(k, 12, seeds, init)
            for m in rng.sample(range(sum(a)+1), min(100, sum(a)+1)):
                assert oracle.signed(m) == p.get(m, 0)
            random_cases += 1
    report["random_seed_and_sign_cases"] = {"cases": random_cases, "n": 12,
                                            "random_seed": 20260919}

    overlap_checks = 0
    for k in range(2, 7):
        a, e = [0]+weights(k, 14), [1]+coherent_signs(k, 14)
        S, history = [0], [{0: 1}]
        for n in range(1, 15):
            S.append(S[-1] + a[n])
            history.append(signed_sparse(a[1:n+1], e[1:n+1]))
            if n <= k:
                continue
            j, v = n-k-1, a[n-k]
            q = history[j]
            B = sum(history[n-1].get(a[n]+m, 0)*history[n-1].get(m, 0)
                    for m in range(S[j]+1))
            qj = sum(c*c for c in q.values())
            qj1 = sum(c*c for c in history[j+1].values())
            assert e[n]*B == qj-qj1
            for u in range(S[j]+1):
                rhs = e[n]*e[j+1]*(q.get(u-v, 0)-q.get(u+v, 0))
                assert history[n].get(a[n]+u, 0) == rhs
                overlap_checks += 1
    report["pointwise_overlap_identities"] = overlap_checks

    recurrence_checks = 0
    for k in range(2, 31):
        h = count_prefix(k, 1000)
        for n in range(2*k, 1001):
            assert h[n] == sum(h[n-i] for i in range(1, k)) + 2*h[n-2*k]
            recurrence_checks += 1
        for n in (0, 1, k, k+1, 2*k, 99, 200, 1000):
            assert count_fast(k, n) == h[n]
            assert count_fast(k, n, 1_000_000_007) == h[n] % 1_000_000_007
    report["positive_recurrence_checks"] = recurrence_checks
    report["fast_vs_linear"] = {"k_min": 2, "k_max": 30, "n_max": 1000,
                                 "indices_per_k": 8, "exact_and_modular": True}

    # Explicit boundary/failed-naive-approach checks.
    assert signed_sparse([1, 3, 5, 9], [-1]*4)[9] == -2
    assert parity_bitset([1, 2, 3]).bit_count() == 6
    try:
        weights(3, 4, [1, 2, 3])
    except ValueError:
        pass
    else:
        raise AssertionError("non-superincreasing seeds accepted")
    assert count_fast(3, 100, 1) == 0
    report["all_passed"] = True
    report["seconds"] = round(time.perf_counter() - start, 3)
    return report


def growth_constants(k: int) -> tuple[Decimal, Decimal, Decimal]:
    with localcontext() as ctx:
        ctx.prec = 80
        lo, hi = Decimal('0.5'), Decimal(1)
        for _ in range(280):
            r = (lo + hi) / 2
            L = sum(r**j for j in range(1, k)) + 2*r**(2*k)
            if L < 1:
                lo = r
            else:
                hi = r
        r = (lo + hi) / 2
        lam = 1/r
        B = sum(r**j for j in range(k))
        Lp = sum(j*r**(j-1) for j in range(1, k)) + 4*k*r**(2*k-1)
        C = (1 + 2*r**k)*B/(r*Lp)
        lo, hi = Decimal(1), Decimal(2)
        for _ in range(280):
            rho = (lo + hi)/2
            if sum(rho**(-j) for j in range(1, k+1)) > 1:
                lo = rho
            else:
                hi = rho
        rho = (lo+hi)/2
        return +lam, +C, +rho


def artifacts(report: dict) -> None:
    DATA.mkdir(exist_ok=True)
    (DATA / "verification_signed.json").write_text(json.dumps(report, indent=2)+"\n")
    with (DATA / "counts.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["k", "n", "odd_coefficient_count"])
        for k in range(2, 21):
            h = count_prefix(k, 200)
            for n, value in enumerate(h):
                writer.writerow([k, n, value])
    for k in range(2, 11):
        text = "# n h_k(n); proved recurrence, not an assigned OEIS b-file\n"
        text += "\n".join(f"{n} {a}" for n, a in enumerate(count_prefix(k, 200)))+"\n"
        (DATA / f"b_k{k}.txt").write_text(text)
    with (DATA / "growth.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["k", "lambda", "C", "rho_multinacci"])
        for k in range(2, 21):
            writer.writerow([k]+[str(v) for v in growth_constants(k)])
    large = {}
    for k in (2, 3, 4, 5, 10, 20):
        h = count_prefix(k, 10_000)[-1]
        assert h == count_fast(k, 10_000)
        text = str(h)
        large[str(k)] = {"n": 10_000, "decimal_digits": len(text), "value": text,
                         "h_10pow12_mod_1000000007": count_fast(k, 10**12, 1_000_000_007)}
    (DATA / "large_values.json").write_text(json.dumps(large, indent=2)+"\n")


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    result = verify()
    artifacts(result)
    print(json.dumps(result, indent=2))
