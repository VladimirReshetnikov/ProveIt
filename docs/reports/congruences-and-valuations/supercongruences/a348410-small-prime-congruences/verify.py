#!/usr/bin/env python3
"""Exact, standard-library checks for the A348410 supercongruence article.

These finite checks are independent of the written proof. No floating point is
used here. The diagonal coefficient is obtained by an exact two-step recurrence
in the coefficient index, and cross-checked against a binomial sum.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import time
from fractions import Fraction
from functools import lru_cache
from math import comb, gcd
from pathlib import Path
from typing import Iterable


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def valuation(value: int, prime: int) -> int | None:
    """Return v_prime(value); None represents the valuation of zero."""
    if prime < 2:
        raise ValueError("prime must be at least 2")
    if value == 0:
        return None
    value = abs(value)
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def vp_at_least(value: int, prime: int, exponent: int) -> bool:
    return value % (prime ** max(exponent, 0)) == 0


@lru_cache(maxsize=None)
def diagonal(n: int, alpha: int = 2, beta: int = 1) -> int:
    """[x^n](1-x)^(-alpha*n)(1+x)^(-beta*n), for integer parameters.

    If f_k is the coefficient of x^k with n fixed, then
    k*f_k = n*(alpha-beta)*f_(k-1)
            + (n*(alpha+beta)+k-2)*f_(k-2).
    Only two coefficients are stored. Every division is checked to be exact.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    previous2, previous1 = 0, 1  # f_(-1), f_0
    for k in range(1, n + 1):
        numerator = n * (alpha - beta) * previous1
        numerator += (n * (alpha + beta) + k - 2) * previous2
        current, remainder = divmod(numerator, k)
        require(remainder == 0, f"nonintegral coefficient: {(n,alpha,beta,k)}")
        previous2, previous1 = previous1, current
    return previous1


def basket_binomial(n: int, spacing: int = 2) -> int:
    """[x^n](1-x)^(-n)(1-x^spacing)^(-n), by a positive binomial sum."""
    if n < 0 or spacing < 1:
        raise ValueError("n must be nonnegative and spacing positive")
    if n == 0:
        return 1
    return sum(
        comb(2*n-spacing*k-1, n-spacing*k) * comb(n+k-1, k)
        for k in range(n//spacing + 1)
    )


def generalized_binomial(top: int, bottom: int) -> int:
    if bottom < 0:
        return 0
    if top >= 0:
        return comb(top, bottom) if bottom <= top else 0
    return (-1)**bottom * comb(bottom-top-1, bottom)


def signed_binomial(n: int, alpha: int, beta: int) -> int:
    if n == 0:
        return 1
    return sum(
        (-1)**k * generalized_binomial(beta*n+k-1, k)
        * generalized_binomial(alpha*n+n-k-1, n-k)
        for k in range(n+1)
    )


def primes_up_to(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    if bound >= 0:
        sieve[0] = 0
    if bound >= 1:
        sieve[1] = 0
    for p in range(2, int(bound**0.5)+1):
        if sieve[p]:
            sieve[p*p:bound+1:p] = b"\x00" * ((bound-p*p)//p+1)
    return [n for n in range(2, bound+1) if sieve[n]]


def mobius(n: int) -> int:
    result, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
        p += 1
    return -result if n > 1 else result


def divisors(n: int) -> Iterable[int]:
    for d in range(1, int(n**0.5)+1):
        if n % d == 0:
            yield d
            if d*d != n:
                yield n//d


def fraction_mod(value: Fraction, modulus: int) -> int:
    return (value.numerator * pow(value.denominator, -1, modulus)) % modulus


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def run(max_n: int, prime_limit: int, multipliers: int, outdir: Path) -> dict:
    started = time.perf_counter()
    outdir.mkdir(parents=True, exist_ok=True)
    data = outdir / "data"
    data.mkdir(exist_ok=True)
    counts: dict[str, int] = {}

    initial = [1, 1, 5, 19, 85, 376, 1715, 7890, 36693, 171820,
               809380, 3830619, 18201235, 86770516, 414836210]
    require([diagonal(n) for n in range(len(initial))] == initial,
            "initial terms disagree")
    counts["initial_terms"] = len(initial)

    # All terms through 200, followed by predetermined sparse larger indices.
    binomial_indices = set(range(min(max_n, 200)+1))
    binomial_indices.update(n for n in [257, 499, 751, 997, 1499, 2000, 3000]
                            if n <= max_n)
    for n in sorted(binomial_indices):
        require(diagonal(n) == basket_binomial(n), f"binomial mismatch at {n}")
    counts["target_binomial_cross_checks"] = len(binomial_indices)

    for a in range(-3, 4):
        for b in range(-3, 4):
            for n in range(31):
                require(diagonal(n, a, b) == signed_binomial(n, a, b),
                        f"signed binomial mismatch: {(n,a,b)}")
    counts["signed_parameter_binomial_cross_checks"] = 49*31

    target_rows = []
    for p in primes_up_to(prime_limit):
        if p == 2:
            continue
        epsilon = int(p == 3)
        for m in range(1, multipliers+1):
            if m % p == 0:
                continue
            r, n = 1, m*p
            while n <= max_n:
                difference = diagonal(n) - diagonal(n//p)
                exponent = 3*r-epsilon
                require(vp_at_least(difference, p, exponent),
                        f"supercongruence failed: {(p,m,r)}")
                v = valuation(difference, p)
                target_rows.append({"p":p,"m":m,"r":r,"n":n,
                    "required_exponent":exponent,
                    "actual_valuation":"infinity" if v is None else v,
                    "quotient_mod_p":(difference//p**exponent) % p})
                r += 1
                n *= p
    counts["target_supercongruences"] = len(target_rows)
    write_csv(data/"supercongruence_checks.csv",
              ["p","m","r","n","required_exponent","actual_valuation",
               "quotient_mod_p"], target_rows)

    generalized_count = 0
    for a in range(-3, 4):
        for b in range(-3, 4):
            for p in [3, 5, 7, 11, 13]:
                for m in range(1, 8):
                    if m % p == 0:
                        continue
                    r, n = 1, m*p
                    while n <= min(max_n, 350):
                        difference = diagonal(n,a,b)-diagonal(n//p,a,b)
                        require(vp_at_least(difference,p,3*r-int(p==3)),
                                f"parameter supercongruence failed: {(a,b,p,m,r)}")
                        generalized_count += 1
                        n *= p
                        r += 1
    counts["two_parameter_supercongruences"] = generalized_count

    # Direct local checks of the quadratic-tail lemma. Fractions are reduced
    # modulo p^(t-epsilon), avoiding both floating point and huge rational sums.
    harmonic_checks = 0
    for p in [3,5,7,11,13]:
        for s in range(p, min(max_n,250)+1, p):
            t = valuation(s,p)
            require(t is not None, "positive s has infinite valuation")
            exponent = t-int(p==3)
            if exponent == 0:
                continue
            modulus = p**exponent
            for a,b in [(2,1),(1,1),(2,-3),(-3,2),(0,1),(3,0)]:
                total = sum(
                    (a+b*(-1)**j)*(a+b*(-1)**(s-j))
                    *pow(j*(s-j),-1,modulus)
                    for j in range(1,s) if j % p
                ) % modulus
                require(total == 0, f"quadratic-tail mismatch: {(p,s,a,b)}")
                harmonic_checks += 1
    counts["quadratic_tail_modular_checks"] = harmonic_checks

    term_limit = min(max_n, 1000)
    write_csv(data/"terms.csv", ["n","a_n"],
              [{"n":n,"a_n":diagonal(n)} for n in range(term_limit+1)])
    mobius_rows = []
    for n in range(1, min(max_n, 300)+1):
        raw = sum(mobius(d)*diagonal(n//d) for d in divisors(n))
        primitive, remainder = divmod(raw,n)
        require(remainder == 0 and primitive >= 0, f"necklace failure at {n}")
        part = n
        for p in [2,3]:
            while part % p == 0:
                part //= p
        r3 = valuation(n,3)
        require(r3 is not None, "n is positive")
        factor = part**2 * 3**max(0,2*r3-1)
        require(primitive % factor == 0, f"orbit divisibility failed at {n}")
        lambert = Fraction(raw,n**3)
        denominator = (3*lambert).denominator
        require(denominator & (denominator-1) == 0,
                f"3*Lambert coefficient not dyadic at {n}")
        mobius_rows.append({"n":n,"primitive_orbits":primitive,
            "B_n":str(lambert),"proved_divisor":factor})
    counts["mobius_and_orbit_checks"] = len(mobius_rows)
    write_csv(data/"mobius_invariants.csv",
              ["n","primitive_orbits","B_n","proved_divisor"],mobius_rows)

    # Exact boundary cases, including the period-three counterexample.
    require(diagonal(2)-diagonal(1) == 4, "p=2 boundary")
    require(diagonal(3)-diagonal(1) == 18, "p=3 boundary")
    require(diagonal(5)-diagonal(1) == 375, "p=5 sharpness")
    d3_5 = basket_binomial(5,3)
    require(d3_5 == 201 and (d3_5-1) % 125 == 75,
            "period-three coefficient counterexample")
    c = lambda j: 1+3*int(j%3 == 0)
    bad_sum = sum((Fraction(c(j)*c(5-j),j*j) for j in range(1,5)),Fraction())
    require(bad_sum == Fraction(361,144) and fraction_mod(bad_sum,5) == 4,
            "period-three harmonic counterexample")
    counts["exact_boundary_examples"] = 5

    report = {
        "status":"PASS",
        "scope":"Finite checks support, but do not replace, the article's proofs.",
        "python":platform.python_version(),
        "parameters":{"max_n":max_n,"prime_limit":prime_limit,
                      "multipliers":multipliers},
        "counts":counts,
        "counterexample":{"spacing":3,"a_1":1,"a_5":d3_5,
            "difference_mod_125":75,"harmonic_sum":str(bad_sum),
            "harmonic_sum_mod_5":4},
        "elapsed_seconds":round(time.perf_counter()-started,3),
    }
    (outdir/"verification_report.json").write_text(
        json.dumps(report,indent=2)+"\n",encoding="utf-8")
    lines = ["A348410 exact verification: PASS", report["scope"], ""]
    lines += [f"{key}: {value}" for key,value in counts.items()]
    lines += ["",f"Elapsed: {report['elapsed_seconds']} seconds",
              "Period-three counterexample: a(5)-a(1)=200, not divisible by 125.",
              "Weighted harmonic counterexample: 361/144 = 4 (mod 5)."]
    (outdir/"verification_report.txt").write_text("\n".join(lines)+"\n",encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n",type=int,default=3000)
    parser.add_argument("--prime-limit",type=int,default=97)
    parser.add_argument("--multipliers",type=int,default=12)
    parser.add_argument("--output-dir",type=Path,default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    if args.max_n < 20 or args.prime_limit < 5 or args.multipliers < 1:
        parser.error("max-n >= 20, prime-limit >= 5, and multipliers >= 1 are required")
    print(json.dumps(run(args.max_n,args.prime_limit,args.multipliers,args.output_dir),indent=2))


if __name__ == "__main__":
    main()
