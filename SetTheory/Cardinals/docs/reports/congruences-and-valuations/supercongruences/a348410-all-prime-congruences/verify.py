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


def basket_convolution(n: int) -> int:
    """a(n), by repeated convolution of the single-pair series floor(j/2)+1.

    This is a fourth, structurally independent evaluation mechanism: it never
    forms a binomial coefficient and never divides. It is quadratic in n per
    convolution, so it is used only for small indices.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    values = [1] + [0]*n
    for _ in range(n):
        values = [sum(values[j-k]*(k//2 + 1) for k in range(j+1))
                  for j in range(n+1)]
    return values[n]


def power_coefficients(alpha: int, beta: int, power: int, degree: int):
    """Yield [x^j](1-x)^(-alpha*power)(1+x)^(-beta*power) for 0 <= j <= degree.

    Same exact recurrence as `diagonal`, but with the exponent multiplier and
    the extraction degree decoupled. Divisions stay exact integer divisions;
    they are never replaced by a modular inverse.
    """
    if power < 0 or degree < 0:
        raise ValueError("power and degree must be nonnegative")
    previous2, previous1 = 0, 1
    yield 1
    for j in range(1, degree+1):
        numerator = power*(alpha-beta)*previous1
        numerator += (power*(alpha+beta) + j - 2)*previous2
        current, remainder = divmod(numerator, j)
        require(remainder == 0, f"nonexact coefficient division at j={j}")
        yield current
        previous2, previous1 = previous1, current


def series_mul(a: list, b: list, size: int) -> list:
    result = [0]*size
    for i, ai in enumerate(a[:size]):
        if ai:
            for j, bj in enumerate(b[:size-i]):
                result[i+j] += ai*bj
    return result


def series_add(*terms: list) -> list:
    size = max(map(len, terms))
    return [sum(term[i] if i < len(term) else 0 for term in terms)
            for i in range(size)]


def series_scale(a: list, scalar: int) -> list:
    return [scalar*value for value in a]


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

    # The values displayed in the OEIS entry inspected on 2026-09-19.
    initial = [1, 1, 5, 19, 85, 376, 1715, 7890, 36693, 171820,
               809380, 3830619, 18201235, 86770516, 414836210,
               1988138644, 9548771157, 45948159420, 221470766204,
               1069091485500, 5167705849460, 25009724705460,
               121171296320475, 587662804774890, 2852708925078675,
               13859743127937876]
    require([diagonal(n) for n in range(len(initial))] == initial,
            "initial terms disagree")
    counts["initial_terms"] = len(initial)

    # A fourth evaluation mechanism, independent of every binomial identity.
    for n in range(13):
        require(diagonal(n) == basket_convolution(n),
                f"basket convolution mismatch at {n}")
    counts["basket_convolution_cross_checks"] = 13

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
            # Multipliers divisible by p are deliberately NOT skipped: they
            # are what exercises the strong exponent 3(r+v_p(m))-eps_p.
            vm = valuation(m, p) or 0
            r, n = 1, m*p
            while n <= max_n:
                difference = diagonal(n) - diagonal(n//p)
                exponent = 3*(r+vm)-epsilon
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
    counts["largest_target_index_tested"] = max(row["n"] for row in target_rows)
    write_csv(data/"supercongruence_checks.csv",
              ["p","m","r","n","required_exponent","actual_valuation",
               "quotient_mod_p"], target_rows)

    generalized_count = 0
    for a in range(-3, 4):
        for b in range(-3, 4):
            for p in [3, 5, 7, 11, 13]:
                for m in range(1, 8):
                    vm = valuation(m, p) or 0
                    r, n = 1, m*p
                    while n <= min(max_n, 350):
                        difference = diagonal(n,a,b)-diagonal(n//p,a,b)
                        require(vp_at_least(difference,p,3*(r+vm)-int(p==3)),
                                f"parameter supercongruence failed: {(a,b,p,m,r)}")
                        generalized_count += 1
                        n *= p
                        r += 1
    counts["two_parameter_supercongruences"] = generalized_count

    # Lemma "Logarithmic-derivative estimate": v_p([x^j]Phi^L) >=
    # max(0, v_p(L)-v_p(j)). The diagonal tests never exercise this directly.
    derivative_checks = 0
    for a, b in [(2,1), (-2,3), (3,4), (0,0), (1,1)]:
        for p in [3, 5, 7]:
            for r in [1, 2, 3]:
                power = p**r
                for j, value in enumerate(
                        power_coefficients(a, b, power, power+10)):
                    if j == 0:
                        require(value == 1, "constant term must be one")
                        continue
                    bound = max(0, r - (valuation(j, p) or 0))
                    require(vp_at_least(value, p, bound),
                            f"derivative coefficient bound: {(a,b,p,r,j)}")
                    derivative_checks += 1
    counts["derivative_coefficient_bounds"] = derivative_checks

    # Lemma "Exponential truncation": every discarded term k>=3 of the formal
    # exponential satisfies k*r - v_p(k!) >= 3r - eps_p.
    tail_checks = 0
    for p in primes_up_to(prime_limit):
        if p == 2:
            continue
        for r in range(1, 6):
            factorial_valuation = 0
            for k in range(1, 1001):
                factorial_valuation += valuation(k, p) or 0
                if k >= 3:
                    require(k*r - factorial_valuation >= 3*r - int(p == 3),
                            f"exponential tail bound: {(p,r,k)}")
                    tail_checks += 1
    counts["exponential_tail_inequalities"] = tail_checks

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
    mobius_denominator_checks = 0
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
        if n <= 100:
            # The cubic-transform denominator predicates, stated directly.
            reduced = lambert.denominator
            for q in primes_up_to(100):
                if q >= 5:
                    require(reduced % q != 0,
                            f"denominator divisible by {q} at n={n}")
            require(reduced % 9 != 0, f"denominator divisible by 9 at n={n}")
            if n % 2:
                require((3*lambert).denominator == 1,
                        f"3*B(n) not integral at odd n={n}")
            mobius_denominator_checks += 1
        mobius_rows.append({"n":n,"primitive_orbits":primitive,
            "B_n":str(lambert),"proved_divisor":factor})
    counts["mobius_and_orbit_checks"] = len(mobius_rows)
    counts["cubic_mobius_denominator_checks"] = mobius_denominator_checks
    write_csv(data/"mobius_invariants.csv",
              ["n","primitive_orbits","B_n","proved_divisor"],mobius_rows)

    # Exact generating-function checks, in integer arithmetic only. The SymPy
    # run in symbolic_checks.py is an independent second mechanism.
    size = 61
    coefficients = [diagonal(n) for n in range(size)]
    y = [0]
    for n in range(1, size):
        last = 1
        for last in power_coefficients(2, 1, n, n-1):
            pass
        quotient, remainder = divmod(last, n)
        require(remainder == 0, f"log-y coefficient not integral at {n}")
        y.append(quotient)
    y2 = series_mul(y, y, size)
    y3 = series_mul(y2, y, size)
    y4 = series_mul(y2, y2, size)
    require(series_add(y, series_scale(y2,-1), series_scale(y3,-1), y4)
            == [0,1] + [0]*(size-2), "inverse defining polynomial y-y^2-y^3+y^4=z")
    denominator_series = series_add([1] + [0]*(size-1),
                                    series_scale(y,-1), series_scale(y2,-4))
    require(series_mul(denominator_series, coefficients, size)
            == series_add([1] + [0]*(size-1), series_scale(y2,-1)),
            "parametric generating function (1-y-4y^2)H = 1-y^2")
    h2 = series_mul(coefficients, coefficients, size)
    h3 = series_mul(h2, coefficients, size)
    h4 = series_mul(h2, h2, size)
    quartic = series_add(
        series_mul([-32,107,256], series_add(h4, series_scale(h3,-1)), size),
        series_mul([0,36,96], h2, size),
        series_mul([0,-4,-16], coefficients, size),
        [0,0,1] + [0]*(size-3))
    require(all(value == 0 for value in quartic),
            "quartic generating function, integer arithmetic")
    counts["generating_function_coefficients"] = size

    # Exact boundary cases, including the period-three counterexamples.
    require(diagonal(2)-diagonal(1) == 4, "p=2 boundary")
    require(diagonal(3)-diagonal(1) == 18, "p=3 boundary")
    require(diagonal(5)-diagonal(1) == 375, "p=5 sharpness")
    require(diagonal(25)-diagonal(5) == 13859743127937500
            and valuation(diagonal(25)-diagonal(5), 5) == 6,
            "large odd-prime example a(25)-a(5)")
    d3_5 = basket_binomial(5,3)
    require(d3_5 == 201 and (d3_5-1) % 125 == 75,
            "period-three coefficient counterexample")
    c = lambda j: 1+3*int(j%3 == 0)
    bad_sum = sum((Fraction(c(j)*c(5-j),j*j) for j in range(1,5)),Fraction())
    require(bad_sum == Fraction(361,144) and fraction_mod(bad_sum,5) == 4,
            "period-three harmonic counterexample, input V_1")
    # The same failure certified directly in the quadratic coefficient.
    direct = 2*sum((Fraction(c(j)*c(5-j), j*(5-j)) for j in range(1,3)),
                   Fraction())
    require(direct == Fraction(11,6) and fraction_mod(direct,5) == 1,
            "direct quadratic coefficient 11/6")
    counts["exact_boundary_examples"] = 7

    # The infinite period-three family: v_5(b_t(5)-b_t(1)) = 2 exactly.
    boundary_rows = []
    for t in [1, 3, 9]:
        b_one = t
        b_five = comb(5*t+4, 5) + 5*t*comb(5*t+1, 2)
        require(valuation(b_five-b_one, 5) == 2,
                f"period-three family exact valuation at t={t}")
        require((b_five-b_one) % 125 == (25*t*t*pow(2,-1,125)) % 125,
                f"period-three family residue at t={t}")
        boundary_rows.append({"t":t,"b_t_1":b_one,"b_t_5":b_five,
                              "difference":b_five-b_one,
                              "residue_mod_125":(b_five-b_one) % 125})
    counts["period_three_family_members"] = len(boundary_rows)
    write_csv(data/"period_three_counterexamples.csv",
              ["t","b_t_1","b_t_5","difference","residue_mod_125"],
              boundary_rows)

    # Framing-audit appendix: the second audit input V_3, defined over Q
    # alone. Its rational 2-function condition is PROVED in the appendix;
    # this is a finite confirmation, not the proof.
    c3 = lambda j: 3+9*int(j%3 == 0)
    audit_sum = sum((Fraction(c3(5-k)*c3(k),k*k) for k in range(1,5)),
                    Fraction())
    require(audit_sum == Fraction(361,16) and fraction_mod(audit_sum,5) == 1,
            "audit harmonic sum 361/16 = 1 (mod 5)")
    audit_quadratic = 2*sum((Fraction(c3(j)*c3(5-j), j*(5-j))
                             for j in range(1,3)), Fraction())
    require(audit_quadratic == Fraction(33,2)
            and fraction_mod(audit_quadratic,5) != 0,
            "audit quadratic coefficient 33/2")
    require(comb(19,5) + 15*comb(16,2) == 13428
            and (13428-3) % 125 == 50, "audit framing values")
    rational_two_checks = 0
    for p in primes_up_to(prime_limit):
        for r in range(1, 5):
            for m in range(1, 101):
                require(vp_at_least(c3(m*p**r)-c3(m*p**(r-1)), p, 2*r),
                        f"rational 2-function input: {(p,r,m)}")
                rational_two_checks += 1
    counts["rational_two_function_input_checks"] = rational_two_checks

    report = {
        "status":"PASS",
        "scope":"Finite checks support, but do not replace, the article's proofs.",
        "python":platform.python_version(),
        "parameters":{"max_n":max_n,"prime_limit":prime_limit,
                      "multipliers":multipliers},
        "counts":counts,
        "counterexample_V1":{"spacing":3,"b_1":1,"b_5":d3_5,
            "difference_mod_125":75,"harmonic_sum":str(bad_sum),
            "harmonic_sum_mod_5":4,
            "direct_quadratic_coefficient":str(direct)},
        "counterexample_V3":{"spacing":3,"framing_1":3,"framing_5":13428,
            "difference_mod_125":50,"harmonic_sum":str(audit_sum),
            "harmonic_sum_mod_5":1,
            "direct_quadratic_coefficient":str(audit_quadratic)},
        "elapsed_seconds":round(time.perf_counter()-started,3),
    }
    (outdir/"verification_report.json").write_text(
        json.dumps(report,indent=2)+"\n",encoding="utf-8")
    lines = ["A348410 exact verification: PASS", report["scope"], ""]
    lines += [f"{key}: {value}" for key,value in counts.items()]
    lines += ["",f"Elapsed: {report['elapsed_seconds']} seconds",
              "Period-three counterexample (input V_1, over Q(sqrt(-3))):",
              "  b(5)-b(1)=200, not divisible by 125; harmonic sum 361/144 = 4 (mod 5);",
              "  quadratic coefficient 11/6 = 1 (mod 5).",
              "Period-three counterexample (input V_3, over Q at every prime):",
              "  fr(5)-fr(1)=13425 = 50 (mod 125); harmonic sum 361/16 = 1 (mod 5);",
              "  quadratic coefficient 33/2 = 4 (mod 5).",
              "The two harmonic values are for DIFFERENT inputs; neither is a typo."]
    (outdir/"verification_report.txt").write_text("\n".join(lines)+"\n",encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n",type=int,default=5000,
                        help="largest index in the original-sequence sweep")
    parser.add_argument("--prime-limit",type=int,default=97)
    parser.add_argument("--multipliers",type=int,default=12)
    parser.add_argument("--output-dir",type=Path,default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    if args.max_n < 20 or args.prime_limit < 5 or args.multipliers < 1:
        parser.error("max-n >= 20, prime-limit >= 5, and multipliers >= 1 are required")
    print(json.dumps(run(args.max_n,args.prime_limit,args.multipliers,args.output_dir),indent=2))


if __name__ == "__main__":
    main()
