#!/usr/bin/env python3
"""Exact, finite regression checks for the elementary chapter.

This file checks finite ranges. It is not a mathematical proof, a Lean build,
or a verification of object-language iPRA derivations. All calculations use
Python integers; no floating-point approximations or probabilistic tests occur.
Run: python3 code/elementary_checks.py --output verification/elementary_checks.json
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
import math
from pathlib import Path
from time import perf_counter


def require(condition: bool, context: object) -> None:
    if not condition:
        raise AssertionError(context)


def division_clock(a: int, b: int) -> tuple[int, int]:
    """The counter construction of el:division, with exactly a steps."""
    if a < 0 or b <= 0:
        raise ValueError("a >= 0 and b > 0 required")
    q = r = 0
    for _ in range(a):
        if r + 1 < b:
            r += 1
        else:
            q += 1
            r = 0
    return q, r


def extended_gcd_clock(a: int, b: int, audit: bool = False) -> tuple[int, int, int]:
    """The absorbing Euclidean loop, with the report's supplied clock."""
    if a < 0 or b < 0:
        raise ValueError("nonnegative inputs required")
    x, y, u, v, r, s = a, b, 1, 0, 0, 1
    bound = 1
    for i in range(a + b + 1):
        if audit:
            require(x == u*a + v*b and y == r*a + s*b,
                    ("Bezout invariant", a, b, i))
            require(y == 0 or y + i <= b, ("Euclid descent", a, b, i, y))
            require(max(abs(u), abs(v), abs(r), abs(s)) <= bound,
                    ("coefficient bound", a, b, i))
        if y:
            q, rem = division_clock(x, y)
            x, y, u, v, r, s = y, rem, r, s, u-q*r, v-q*s
        bound *= a + b + 2
    require(y == 0, ("Euclid clock exhausted", a, b))
    if audit:
        require(x == u*a + v*b, ("final Bezout", a, b))
        require(max(abs(u), abs(v), abs(r), abs(s)) <= bound,
                ("final coefficient bound", a, b))
    return x, u, v


def generalized_crt(moduli: tuple[int, ...], residues: tuple[int, ...]):
    """Merge constraints using the constructive two-modulus theorem."""
    if len(moduli) != len(residues) or any(m <= 0 for m in moduli):
        raise ValueError("equally sized arrays and positive moduli required")
    x, modulus = 0, 1
    for m, a in zip(moduli, residues):
        g, u, _ = extended_gcd_clock(modulus, m)
        delta = a - x
        if delta % g:
            return None
        reduced_m = m // g
        t = ((delta // g) * u) % reduced_m
        x = (x + modulus*t) % (modulus*reduced_m)
        modulus *= reduced_m
    return x, modulus


def brute_crt(moduli: tuple[int, ...], residues: tuple[int, ...]):
    modulus = math.lcm(*moduli)
    witnesses = [x for x in range(modulus)
                 if all(x % m == a % m for m, a in zip(moduli, residues))]
    require(len(witnesses) <= 1, ("CRT uniqueness in reference search", moduli, residues))
    return (witnesses[0], modulus) if witnesses else None


def trial_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def factor_clock(n: int) -> list[int]:
    """n absorbing stages, each with a bounded least-divisor scan."""
    if n < 1:
        raise ValueError("positive integer required")
    remainder, factors = n, []
    for _ in range(n):
        if remainder > 1:
            p = next(d for d in range(2, remainder + 1) if remainder % d == 0)
            factors.append(p)
            remainder //= p
    require(remainder == 1, ("factor clock exhausted", n))
    return factors


def sieve(N: int) -> list[bool]:
    alive = [n >= 2 for n in range(N + 1)]
    for d in range(2, math.isqrt(N) + 1):
        if alive[d]:
            for n in range(d*d, N + 1, d):
                alive[n] = False
    return alive


def valuation_division(p: int, n: int) -> int:
    """Independent valuation calculation, clocked by binary length."""
    if p < 2 or n <= 0:
        raise ValueError("p >= 2 and n > 0 required")
    exponent, residual = 0, n
    for _ in range(n.bit_length() + 1):
        if residual % p == 0:
            exponent += 1
            residual //= p
    require(residual % p != 0, ("valuation clock exhausted", p, n))
    return exponent


def lucas_digit_product(p: int, n: int, k: int) -> int:
    a, b, result = n, k, 1
    for _ in range(n + k + 1):
        na, kb = a % p, b % p
        coefficient = math.comb(na, kb) if kb <= na else 0
        result = (result * coefficient) % p
        a //= p
        b //= p
    require(a == b == 0, ("digit clock exhausted", p, n, k))
    return result


def carry_count(p: int, a: int, b: int) -> int:
    x, y, carry, total = a, b, 0, 0
    for _ in range(a + b + 2):
        carry = (x % p + y % p + carry) // p
        require(carry in (0, 1), ("carry not Boolean", p, a, b))
        total += carry
        x //= p
        y //= p
    require(x == y == carry == 0, ("carry clock exhausted", p, a, b))
    return total


def digit_sum(p: int, n: int) -> int:
    x, total = n, 0
    for _ in range(n + 1):
        total += x % p
        x //= p
    require(x == 0, ("digit-sum clock exhausted", p, n))
    return total


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def phi(n: int) -> int:
    return sum(math.gcd(a, n) == 1 for a in range(1, n + 1))


def mu_from_factors(factors: list[int]) -> int:
    return 0 if len(set(factors)) != len(factors) else (-1)**len(factors)


def sigma_by_paired_divisors(n: int) -> int:
    total = 0
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            total += d
            if d*d != n:
                total += n // d
    return total


def run_checks() -> dict:
    start = perf_counter()
    checks = {}

    count = 0
    for a in range(81):
        for b in range(1, 18):
            actual = division_clock(a, b)
            require(actual == divmod(a, b), ("division", a, b, actual))
            count += 1
    checks["division"] = {"status": "passed", "cases": count,
        "range": "0<=a<=80, 1<=b<=17", "reference": "Python divmod"}

    count = 0
    for a in range(46):
        for b in range(46):
            g, u, v = extended_gcd_clock(a, b, audit=True)
            require(g == math.gcd(a, b), ("gcd value", a, b, g))
            require(u*a + v*b == g, ("gcd witness", a, b, u, v))
            bound = (a+b+2)**(a+b+1)
            require(abs(u) <= bound and abs(v) <= bound, ("Bezout final bound", a, b))
            count += 1
    checks["extended_gcd"] = {"status": "passed", "cases": count,
        "range": "0<=a,b<=45, including (0,0)",
        "verified": ["math.gcd agreement", "Bezout identity at every step",
                     "decreasing second-remainder invariant", "coefficient bound at every step",
                     "termination by a+b+1"]}

    count = 0
    for arity, maximum in ((2, 10), (3, 5)):
        for moduli in product(range(1, maximum+1), repeat=arity):
            for residues in product(*(range(m) for m in moduli)):
                actual = generalized_crt(moduli, residues)
                expected = brute_crt(moduli, residues)
                require(actual == expected, ("CRT", moduli, residues, actual, expected))
                compatible = all((residues[i]-residues[j]) % math.gcd(moduli[i],moduli[j]) == 0
                                 for i in range(arity) for j in range(arity))
                require((actual is not None) == compatible,
                        ("CRT compatibility criterion", moduli, residues))
                count += 1
    corners = [((), ()), ((1,), (-9,)), ((4,6,9), (-5,7,-8)),
               ((6,10,15), (-7,13,-2)), ((4,6), (-3,-2))]
    for moduli, residues in corners:
        require(generalized_crt(moduli,residues) == brute_crt(moduli,residues),
                ("signed or empty CRT",moduli,residues))
        count += 1
    checks["generalized_crt"] = {"status": "passed", "cases": count,
        "range": "all residue systems for two moduli 1..10 and three moduli 1..5; five signed/empty corners",
        "reference": "exhaustive search below math.lcm; independent pairwise gcd compatibility test"}

    comparisons = 0
    for N in range(201):
        flags = sieve(N)
        for n, flag in enumerate(flags):
            require(flag == trial_prime(n), ("sieve", N, n, flag))
            comparisons += 1
    checks["sieve"] = {"status": "passed", "input_bounds": 201,
        "entry_comparisons": comparisons, "range": "0<=N<=200, every entry 0..N",
        "reference": "independent trial division up to integer square root"}

    lucas_cases = kummer_cases = 0
    primes = [2,3,5,7,11,13,17]
    for p in primes:
        for n in range(71):
            for k in range(n+5):
                coefficient = math.comb(n,k) if k <= n else 0
                require(lucas_digit_product(p,n,k) == coefficient % p,
                        ("Lucas",p,n,k))
                lucas_cases += 1
                if k <= n:
                    v = valuation_division(p,coefficient)
                    require(carry_count(p,k,n-k) == v, ("Kummer",p,n,k))
                    require((p-1)*v == digit_sum(p,k)+digit_sum(p,n-k)-digit_sum(p,n),
                            ("Kummer digit sum",p,n,k))
                    kummer_cases += 1
    checks["lucas"] = {"status": "passed", "cases": lucas_cases,
        "primes": primes, "range": "0<=n<=70, 0<=k<=n+4",
        "reference": "exact math.comb modulo p, including k>n"}
    checks["kummer"] = {"status": "passed", "cases": kummer_cases,
        "primes": primes, "range": "0<=k<=n<=70",
        "reference": "division valuation of exact math.comb; separately checked digit-sum formula"}

    limit = 400
    divs = {n: divisors(n) for n in range(1,limit+1)}
    factors = {n: factor_clock(n) for n in range(1,limit+1)}
    phis = {n: phi(n) for n in range(1,limit+1)}
    mus = {n: mu_from_factors(factors[n]) for n in range(1,limit+1)}
    for n in range(1,limit+1):
        fs, ds = factors[n], divs[n]
        exponents = Counter(fs)
        require(fs == sorted(fs) and all(trial_prime(p) for p in fs)
                and math.prod(fs) == n, ("factorization",n,fs))
        require(len(ds) == math.prod(e+1 for e in exponents.values()), ("tau formula",n))
        for r in range(3):
            formula = math.prod(sum(p**(r*j) for j in range(e+1))
                                for p,e in exponents.items())
            require(sum(d**r for d in ds) == formula, ("sigma formula",r,n))
        require(phis[n] == math.prod(p**(e-1)*(p-1) for p,e in exponents.items()),
                ("phi product",n))
        require(sum(phis[d] for d in ds) == n, ("phi divisor sum",n))
        require(sum(mus[d] for d in ds) == int(n==1), ("Mobius cancellation",n))
        require(sum(mus[d]*(n//d) for d in ds) == phis[n], ("phi Mobius identity",n))
        square = math.isqrt(n)**2 == n
        twice_square = n%2 == 0 and math.isqrt(n//2)**2 == n//2
        require(len(ds)%2 == int(square), ("tau parity",n))
        require(sum(ds)%2 == int(square or twice_square), ("sigma parity",n))
        require(sum((-1)**len(factors[d]) for d in ds) == int(square),
                ("Liouville square detection",n))
        squarefree = math.prod(p**(e%2) for p,e in exponents.items())
        root = math.prod(p**(e//2) for p,e in exponents.items())
        require(squarefree*root*root == n and all(squarefree%(p*p) for p in exponents),
                ("squarefree decomposition",n))
    inversion_cases = 0
    for f in (lambda n:n*n-3*n+2, lambda n:(-1)**n, lambda n:n*n*n+n):
        F = {n:sum(f(d) for d in divs[n]) for n in range(1,limit+1)}
        for n in range(1,limit+1):
            require(sum(mus[d]*F[n//d] for d in divs[n]) == f(n),
                    ("Mobius inversion",n))
            inversion_cases += 1
    multiplicative_cases = 0
    for a in range(1,21):
        for b in range(1,21):
            if math.gcd(a,b)==1:
                for values in (phis,mus):
                    require(values[a*b] == values[a]*values[b], ("multiplicativity",a,b))
                require(len(divs[a*b])==len(divs[a])*len(divs[b]), ("tau multiplicativity",a,b))
                require(sum(divs[a*b])==sum(divs[a])*sum(divs[b]), ("sigma multiplicativity",a,b))
                multiplicative_cases += 1
    checks["arithmetic_functions"] = {"status": "passed", "positive_inputs": limit,
        "range": "1<=n<=400; sigma_r for r=0,1,2; coprime a,b<=20",
        "mobius_inversion_cases": inversion_cases, "multiplicative_input_pairs": multiplicative_cases,
        "verified": ["bounded prime-factor construction", "tau and sigma product formulas",
            "phi product and divisor-sum formulas", "Mobius cancellation and inversion for three signed functions",
            "phi via Mobius", "squarefree decomposition", "tau/sigma parity",
            "Liouville square indicator", "multiplicativity of phi, mu, tau, sigma"]}

    perfect_limit = 10000
    observed = [n for n in range(2,perfect_limit+1,2)
                if sigma_by_paired_divisors(n) == 2*n]
    constructed = []
    for e in range(2,perfect_limit.bit_length()+1):
        q = 2**e-1
        candidate = 2**(e-1)*q
        if trial_prime(q) and candidate <= perfect_limit:
            require(trial_prime(e), ("Mersenne exponent",e))
            constructed.append(candidate)
    require(observed == constructed == [6,28,496,8128],
            ("even perfect numbers",observed,constructed))
    for n in observed:
        e = valuation_division(2,n)+1
        require(n == 2**(e-1)*(2**e-1) and trial_prime(2**e-1),
                ("recovered perfect exponent",n,e))
    checks["even_perfect_numbers"] = {"status": "passed", "even_inputs": perfect_limit//2,
        "range": "2<=N<=10000, N even", "observed": observed,
        "reference": "independent paired-divisor sigma versus Mersenne-prime construction and recovered exponents"}

    return {"status":"passed", "scope":"exact finite regression checks only; not proofs or formalization",
            "report_date":"2026-11-22", "arithmetic":"arbitrary-precision integers; no floating-point tests",
            "checks":checks, "elapsed_seconds":round(perf_counter()-start,3)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    default = Path(__file__).resolve().parents[1] / "verification" / "elementary_checks.json"
    parser.add_argument("--output", type=Path, default=default)
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":result["status"],"groups":len(result["checks"]),
                      "elapsed_seconds":result["elapsed_seconds"],"output":str(args.output)}))


if __name__ == "__main__":
    main()
