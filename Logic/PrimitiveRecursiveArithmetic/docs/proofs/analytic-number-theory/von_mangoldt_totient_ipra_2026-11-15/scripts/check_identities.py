#!/usr/bin/env python3
"""Finite regression checks for the accompanying iPRA proof report.

This is not a proof of universal statements.  It independently checks the
primitive-recursive definitions and many theorem instances with exact integer
or Fraction arithmetic.  Polynomial checks use SymPy over ZZ.
"""
from __future__ import annotations

import json
import math
import sys
from dataclasses import dataclass, asdict
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable

try:
    import sympy as sp
except Exception as exc:  # pragma: no cover
    raise SystemExit(f"SymPy is required for polynomial checks: {exc}")


@dataclass
class Check:
    name: str
    cases: int
    passed: bool
    details: str = ""


CHECKS: list[Check] = []


def record(name: str, cases: int, failures: list[str], details: str = "") -> None:
    if failures:
        details = (details + " | " if details else "") + "; ".join(failures[:8])
    CHECKS.append(Check(name, cases, not failures, details))


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def factor(n: int) -> dict[int, int]:
    if n < 1:
        return {}
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors(n: int) -> list[int]:
    ds = [1]
    for p, a in factor(n).items():
        ds = [d * p**e for d in ds for e in range(a + 1)]
    return sorted(ds)


def mobius(n: int) -> int:
    fs = factor(n)
    if any(a > 1 for a in fs.values()):
        return 0
    return -1 if len(fs) % 2 else 1


def phi_factor(n: int) -> int:
    if n == 0:
        return 0
    ans = n
    for p in factor(n):
        ans = ans // p * (p - 1)
    return ans


def phi_count(n: int) -> int:
    if n == 0:
        return 0
    return sum(math.gcd(a, n) == 1 for a in range(n))


def sigma(n: int) -> int:
    return sum(divisors(n))


def tau(n: int) -> int:
    z = 1
    for a in factor(n).values():
        z *= a + 1
    return z


def rad(n: int) -> int:
    z = 1
    for p in factor(n):
        z *= p
    return z


def lcm_upto(n: int) -> int:
    z = 1
    for k in range(1, n + 1):
        z = math.lcm(z, k)
    return z


def prime_power(n: int) -> tuple[int, int] | None:
    if n < 2:
        return None
    fs = factor(n)
    if len(fs) != 1:
        return None
    return next(iter(fs.items()))


def weight(p: int) -> int:
    # Deliberately non-logarithmic PR weight; all weighted identities should
    # be independent of the choice.
    return 2 * p + 1


def Lw(n: int) -> int:
    return sum(a * weight(p) for p, a in factor(n).items())


def Lambda_w(n: int) -> int:
    pp = prime_power(n)
    return 0 if pp is None else weight(pp[0])


def Psi_w(n: int) -> int:
    return sum(Lambda_w(k) for k in range(1, n + 1))


def multiplicative_order(a: int, n: int) -> int:
    if math.gcd(a, n) != 1:
        raise ValueError("a must be a unit")
    if n == 1:
        return 1
    x = 1
    for k in range(1, phi_factor(n) + 1):
        x = (x * a) % n
        if x == 1:
            return k
    raise AssertionError("Euler bound failed")


def check_basic_phi(max_n: int = 500) -> None:
    failures: list[str] = []
    cases = 0
    for n in range(max_n + 1):
        cases += 1
        if phi_count(n) != phi_factor(n):
            failures.append(f"n={n}: count={phi_count(n)}, factor={phi_factor(n)}")
    record("totient counting definition equals product implementation", cases, failures)


def check_divisor_phi(max_n: int = 500) -> None:
    failures = []
    cases = 0
    for n in range(1, max_n + 1):
        cases += 1
        if sum(phi_factor(d) for d in divisors(n)) != n:
            failures.append(f"n={n}")
        m1 = sum(mobius(d) * (n // d) for d in divisors(n))
        m2 = sum(d * mobius(n // d) for d in divisors(n))
        if m1 != phi_factor(n) or m2 != phi_factor(n):
            failures.append(f"Mobius n={n}: {m1},{m2}")
    record("sum phi over divisors and both Mobius formulas", cases * 3, failures)


def check_phi_calculus() -> None:
    failures: list[str] = []
    cases = 0
    for n in range(1, 101):
        for k in range(1, 6):
            cases += 1
            if phi_factor(n**k) != n ** (k - 1) * phi_factor(n):
                failures.append(f"power n={n},k={k}")
        cases += 1
        if phi_factor(rad(n)) * n != phi_factor(n) * rad(n):
            failures.append(f"rad n={n}")
        cases += 1
        lhs = sum(Fraction(mobius(d) ** 2, phi_factor(d)) for d in divisors(n))
        rhs = Fraction(n, phi_factor(n))
        if lhs != rhs:
            failures.append(f"squarefree sum n={n}: {lhs}!={rhs}")
        cases += 1
        if phi_factor(2 * n) != (phi_factor(n) if n % 2 else 2 * phi_factor(n)):
            failures.append(f"double n={n}")
    for a in range(1, 101):
        for b in range(a, 301, a):
            cases += 1
            if phi_factor(b) % phi_factor(a) != 0:
                failures.append(f"divisibility {a}|{b}")
    for m in range(1, 61):
        for n in range(1, 61):
            d = math.gcd(m, n)
            cases += 2
            if phi_factor(m * n) * phi_factor(d) != phi_factor(m) * phi_factor(n) * d:
                failures.append(f"general mul m={m},n={n}")
            l = math.lcm(m, n)
            if phi_factor(d) * phi_factor(l) != phi_factor(m) * phi_factor(n):
                failures.append(f"gcd/lcm m={m},n={n}")
    record("totient power/divisibility/gcd-lcm/radical identities", cases, failures)


def check_phi_counts(max_n: int = 160) -> None:
    failures: list[str] = []
    cases = 0
    for n in range(1, max_n + 1):
        for d in divisors(n):
            cases += 1
            c = sum(math.gcd(k, n) == d for k in range(n))
            if c != phi_factor(n // d):
                failures.append(f"gcd fiber n={n},d={d}: {c}")
        cases += 1
        s = sum(a for a in range(1, n) if math.gcd(a, n) == 1)
        if n > 1 and 2 * s != n * phi_factor(n):
            failures.append(f"totative sum n={n}")
        cases += 1
        menon = sum(math.gcd(a - 1, n) for a in range(1, n + 1) if math.gcd(a, n) == 1)
        if menon != phi_factor(n) * tau(n):
            failures.append(f"Menon n={n}: {menon}")
    record("gcd fibers, sum of totatives, and Menon identity", cases, failures)


def check_summatory_phi(max_n: int = 300) -> None:
    failures = []
    cases = 0
    total = 0
    for N in range(1, max_n + 1):
        total += phi_factor(N)
        lhs = 2 * total - 1
        rhs = sum(mobius(d) * (N // d) ** 2 for d in range(1, N + 1))
        cases += 1
        if lhs != rhs:
            failures.append(f"N={N}: {lhs}!={rhs}")
    record("summatory totient floor-square identity", cases, failures)


def check_bounds(max_n: int = 5000) -> None:
    failures = []
    cases = 0
    phi_two = []
    for n in range(1, max_n + 1):
        ph = phi_factor(n)
        cases += 1
        if 2 * ph * ph < n:
            failures.append(f"2phi^2 bound n={n}")
        if n not in (2, 6):
            cases += 1
            if ph * ph < n:
                failures.append(f"sqrt bound n={n}")
        if n > 1 and not is_prime(n):
            r = math.isqrt(n)
            cases += 1
            if ph > n - r:
                failures.append(f"composite upper n={n}")
        if n > 1:
            cases += 1
            ratio = Fraction(ph * sigma(n), n * n)
            if not (Fraction(1, 2) < ratio < 1):
                failures.append(f"phi-sigma n={n}: {ratio}")
        if ph == 2:
            phi_two.append(n)
    if phi_two != [3, 4, 6]:
        failures.append(f"phi=2 list={phi_two}")
    record("totient bounds, phi-sigma product, phi(n)=2 classification", cases, failures)


def check_euler_order() -> None:
    failures = []
    cases = 0
    for n in range(1, 121):
        for a in range(0, min(80, 2 * n + 1)):
            if math.gcd(a, n) == 1:
                cases += 1
                if pow(a, phi_factor(n), n) != (1 % n):
                    failures.append(f"Euler a={a},n={n}")
                r = multiplicative_order(a, n)
                if phi_factor(n) % r:
                    failures.append(f"order a={a},n={n},r={r}")
    for a in range(2, 9):
        for m in range(1, 8):
            N = a**m - 1
            cases += 1
            if phi_factor(N) % m:
                failures.append(f"a^m-1 a={a},m={m}")
    for a in range(1, 8):
        for b in range(1, 8):
            if a == b:
                continue
            for n in range(1, 7):
                cases += 1
                N = a**n + b**n
                if phi_factor(N) % n:
                    failures.append(f"plus powers a={a},b={b},n={n}")
    record("Euler theorem, order divisibility, a^m-1 and a^n+b^n", cases, failures)


def check_rsa() -> None:
    failures = []
    cases = 0
    primes = [3, 5, 7, 11, 13]
    for i, p in enumerate(primes):
        for q in primes[i + 1 :]:
            N = p * q
            ph = phi_factor(N)
            for e in range(2, min(ph, 20)):
                if math.gcd(e, ph) != 1:
                    continue
                d = pow(e, -1, ph)
                for x in range(N):
                    cases += 1
                    if pow(pow(x, e, N), d, N) != x:
                        failures.append(f"p={p},q={q},e={e},x={x}")
    record("RSA correctness including nonunit messages", cases, failures)


def check_subbarao(limit: int = 5000) -> None:
    failures = []
    cases = 0
    composite_solutions = []
    for n in range(2, limit + 1):
        ph = phi_factor(n)
        ok = (n * sigma(n) - 2) % ph == 0
        cases += 1
        if is_prime(n) and not ok:
            failures.append(f"prime failed n={n}")
        if not is_prime(n) and ok:
            composite_solutions.append(n)
    if composite_solutions != [4, 6, 22]:
        failures.append(f"composite solutions={composite_solutions}")
    record("Subbarao congruence through 5000", cases, failures,
           f"composite solutions {composite_solutions}")


def check_mangoldt(max_n: int = 400) -> None:
    failures = []
    cases = 0
    for n in range(1, max_n + 1):
        ds = divisors(n)
        cases += 5
        if sum(Lambda_w(d) for d in ds) != Lw(n):
            failures.append(f"divisor sum n={n}")
        if sum(mobius(d) * Lw(n // d) for d in ds) != Lambda_w(n):
            failures.append(f"Mobius 1 n={n}")
        if sum(mobius(n // d) * Lw(d) for d in ds) != Lambda_w(n):
            failures.append(f"Mobius 2 n={n}")
        if n > 1 and sum(mobius(d) * Lw(d) for d in ds) != -Lambda_w(n):
            failures.append(f"Mobius 3 n={n}")
        if sum(mobius(n // d) * Lambda_w(d) for d in ds) != -mobius(n) * Lw(n):
            failures.append(f"mu*Lambda n={n}")
        cases += 1
        if Psi_w(n) != Lw(lcm_upto(n)):
            failures.append(f"psi/lcm n={n}")
        cases += 1
        lhs = Lw(math.factorial(n))
        rhs = sum(Lambda_w(d) * (n // d) for d in range(1, n + 1))
        if lhs != rhs:
            failures.append(f"factorial n={n}")
    record("weighted Mangoldt divisor/Mobius/Psi/factorial identities", cases, failures,
           "weight(p)=2p+1")


def check_lcm_quotient(max_n: int = 150) -> None:
    failures = []
    cases = 0
    prev = 1
    values = []
    for n in range(1, max_n + 1):
        cur = math.lcm(prev, n)
        q = cur // prev
        pp = prime_power(n)
        expected = 1 if pp is None else pp[0]
        cases += 1
        if q != expected:
            failures.append(f"n={n}: q={q},expected={expected}")
        if n <= 20:
            values.append(q)
        prev = cur
    record("lcm quotient equals prime base on prime powers", cases, failures,
           f"first values {values}")


def check_binomial_lcm(max_n: int = 80) -> None:
    failures = []
    cases = 0
    for n in range(1, max_n + 1):
        C = math.comb(2 * n, n)
        interval_prod = 1
        seen: set[int] = set()
        for q in range(n + 1, 2 * n + 1):
            pp = prime_power(q)
            if pp is not None:
                p, _ = pp
                if p in seen:
                    failures.append(f"two powers of p={p} in ({n},{2*n}]")
                seen.add(p)
                interval_prod *= p
        cases += 4
        if C % interval_prod:
            failures.append(f"interval product !| C n={n}")
        if lcm_upto(2 * n) % C:
            failures.append(f"C !| lcm n={n}")
        if C > 4**n:
            failures.append(f"upper C n={n}")
        if C * (2 * n + 1) < 4**n:
            failures.append(f"lower C n={n}")
    record("central binomial/lcm divisibilities and bounds", cases, failures)


def check_cyclotomic(max_n: int = 50) -> None:
    failures = []
    cases = 0
    X = sp.Symbol("X")
    for n in range(1, max_n + 1):
        P = sum(math.gcd(k, n) * X**k for k in range(1, n + 1)) - phi_factor(n)
        Phi = sp.cyclotomic_poly(n, X, polys=True)
        rem = sp.rem(sp.Poly(P, X, domain=sp.ZZ), Phi)
        cases += 1
        if not rem.is_zero:
            failures.append(f"n={n}: remainder={rem.as_expr()}")
    record("cyclotomic polynomial remainder P_n-phi(n)", cases, failures)


def check_examples() -> None:
    failures = []
    cases = 0
    equal_pairs = [1, 3, 15, 104, 164, 194, 255, 495, 584, 975]
    pair_values = []
    for n in equal_pairs:
        cases += 1
        a, b = phi_factor(n), phi_factor(n + 1)
        pair_values.append(a)
        if a != b:
            failures.append(f"pair n={n}: {a}!={b}")
    triple = [phi_factor(n) for n in (5186, 5187, 5188)]
    cases += 3
    if len(set(triple)) != 1 or triple[0] != 2**5 * 3**4:
        failures.append(f"5186 triple={triple}")
    close1 = [phi_factor(n) for n in (25930, 25935, 25940, 25942)]
    cases += 4
    if len(set(close1)) != 1 or close1[0] != 2**7 * 3**4:
        failures.append(f"25930 cluster={close1}")
    close2 = [phi_factor(n) for n in (404471, 404473, 404477)]
    cases += 3
    if len(set(close2)) != 1 or close2[0] != 2**8 * 3**2 * 5**2 * 7:
        failures.append(f"404471 cluster={close2}")
    ap = [phi_factor(n) for n in range(583200, 583351, 30)]
    cases += len(ap)
    if len(set(ap)) != 1 or ap[0] != 155520:
        failures.append(f"equal-totient AP={ap}")
    phisigma_examples = [1, 2, 8, 12, 128, 240, 720, 6912, 32768, 142560, 712800]
    observed = []
    for n in phisigma_examples:
        cases += 1
        val = phi_factor(sigma(n))
        observed.append(val)
        if val != n:
            failures.append(f"phi(sigma({n}))={val}")
    record("MathWorld finite equal-totient and phi(sigma(n)) examples", cases, failures,
           f"pair values {pair_values}; triple {triple}; phi-sigma {observed}")


def check_first_values() -> None:
    expected_phi = [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10]
    got_phi = [phi_factor(n) for n in range(1, 12)]
    expected_exp_lambda = [1, 2, 3, 2, 5, 1, 7, 2]
    got_exp = []
    prev = 1
    for n in range(1, 9):
        cur = math.lcm(prev, n)
        got_exp.append(cur // prev)
        prev = cur
    failures = []
    if got_phi != expected_phi:
        failures.append(f"phi={got_phi}")
    if got_exp != expected_exp_lambda:
        failures.append(f"expLambda={got_exp}")
    record("reference-page initial values", len(got_phi) + len(got_exp), failures,
           f"phi {got_phi}; expLambda {got_exp}")


def main() -> int:
    check_basic_phi()
    check_divisor_phi()
    check_phi_calculus()
    check_phi_counts()
    check_summatory_phi()
    check_bounds()
    check_euler_order()
    check_rsa()
    check_subbarao()
    check_mangoldt()
    check_lcm_quotient()
    check_binomial_lcm()
    check_cyclotomic()
    check_examples()
    check_first_values()

    report = {
        "status": "PASS" if all(c.passed for c in CHECKS) else "FAIL",
        "python": sys.version,
        "sympy": sp.__version__,
        "total_check_groups": len(CHECKS),
        "total_cases": sum(c.cases for c in CHECKS),
        "checks": [asdict(c) for c in CHECKS],
        "disclaimer": "Finite regression evidence only; not a universal proof or a Lean kernel certificate.",
    }
    out = Path(__file__).resolve().parents[1] / "verification_report.json"
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
