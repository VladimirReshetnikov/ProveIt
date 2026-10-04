#!/usr/bin/env python3
"""Exact, finite regression checks for Perfect Transcendence Gaps.

Python 3.10+; standard library only. These checks do NOT certify the
infinitary or descriptive-set-theoretic theorems in the manuscript.
Run: python3 verify.py [--output verification.json]
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import product
import json
from math import factorial, gcd, prod
from pathlib import Path
import random
import sys
from typing import Any

Poly = dict[Fraction, Fraction]
SEED = 20261003


def require(condition: bool, message: str) -> None:
    """Do not use assert: checks must still run under python -O."""
    if not condition:
        raise ArithmeticError(message)


def encode_blocks(digits: tuple[int, ...], width: int) -> int:
    if width < 1 or any(not 0 <= d < (1 << width) for d in digits):
        raise ValueError("Digits do not fit the binary block width.")
    return sum(d << (width * i) for i, d in enumerate(digits))


def recode_blocks(code: int, width: int, prime: int, length: int) -> tuple[int, ...]:
    if code < 0 or width < 1 or prime < 2 or length < 0:
        raise ValueError("Invalid recoding parameters.")
    mask = (1 << width) - 1
    # Reduction modulo p enforces a valid digit even in an arbitrary tail.
    return tuple(((code >> (width * i)) & mask) % prime for i in range(length))


def base_value(digits: tuple[int, ...], base: int) -> int:
    # An independent Horner implementation, least-significant digit first.
    accumulator = 0
    for digit in reversed(digits):
        accumulator = accumulator * base + digit
    return accumulator


def check_digit_recoding() -> dict[str, Any]:
    words = prefixes = contaminated_tails = 0
    per_prime: dict[str, int] = {}
    for p in (2, 3, 5, 7):
        width = (p - 1).bit_length()
        count = 0
        for length in range(6):
            for digits in product(range(p), repeat=length):
                code = encode_blocks(digits, width)
                decoded = recode_blocks(code, width, p, length)
                require(decoded == digits, f"Digit round trip failed: p={p}, {digits}")
                value = base_value(decoded, p)
                require(value == sum(d * p**i for i, d in enumerate(digits)),
                        "Horner and weighted-sum definitions disagree.")
                words += 1
                count += 1
                for n in range(length + 1):
                    require(value % (p**n) == base_value(digits[:n], p),
                            "Prefix residue identity failed.")
                    prefixes += 1
                # Append maximal binary blocks. For odd p these include
                # invalid base-p digits, just as an uncontrolled internal tail may.
                tail = ((1 << width) - 1,) * 3
                extended = code | (encode_blocks(tail, width) << (width * length))
                recoded = recode_blocks(extended, width, p, length + 3)
                require(all(0 <= d < p for d in recoded), "Tail was not normalized.")
                require(base_value(recoded, p) % (p**length) == value,
                        "Uncontrolled higher blocks changed a prescribed prefix.")
                contaminated_tails += 1
        per_prime[str(p)] = count
    return {"status": "PASS", "exhaustive_words": words,
            "prefix_residue_checks": prefixes,
            "arbitrary_tail_checks": contaminated_tails,
            "word_length_range": [0, 5], "words_by_prime": per_prime}


def normalize(f: Poly) -> Poly:
    return {e: c for e, c in f.items() if c}


def multiply(f: Poly, g: Poly) -> Poly:
    result: defaultdict[Fraction, Fraction] = defaultdict(Fraction)
    for e, a in f.items():
        for h, b in g.items():
            result[e + h] += a * b
    return normalize(dict(result))


def scale(f: Poly, scalar: Fraction) -> Poly:
    return normalize({e: scalar * c for e, c in f.items()})


def constant(f: Poly) -> Fraction:
    return f.get(Fraction(0), Fraction(0))


def check_laurent_tails() -> dict[str, Any]:
    rng = random.Random(SEED)
    exponents = tuple(Fraction(-i, 6) for i in range(1, 25))
    checks = 0
    for _ in range(1000):
        def sample() -> Poly:
            result = {e: Fraction(rng.randint(-30, 30), rng.randint(1, 12))
                      for e in rng.sample(exponents, rng.randint(0, 10))}
            result[Fraction(0)] = Fraction(rng.randint(-30, 30))
            return normalize(result)
        f, g = sample(), sample()
        fg = multiply(f, g)
        require(constant(fg) == constant(f) * constant(g),
                "Constant extraction was not multiplicative on nonpositive support.")
        require(all(e <= 0 for e in fg), "Product escaped nonpositive support.")
        checks += 2
        tail = {e: a for e, a in f.items() if e < 0}
        for n in range(1, 13):
            quotient = scale(tail, Fraction(1, n))
            require(scale(quotient, Fraction(n)) == tail, "Tail divisibility failed.")
            # nR consists exactly of series with constant coefficient in nZ.
            f_over_n = scale(f, Fraction(1, n))
            in_r_after_division = constant(f_over_n).denominator == 1
            require(in_r_after_division == (int(constant(f)) % n == 0),
                    "Constant-term criterion for nR failed.")
            require(scale(f_over_n, Fraction(n)) == f, "Exact scalar division failed.")
            checks += 3
    return {"status": "PASS", "seed": SEED, "sample_pairs": 1000,
            "exact_identity_checks": checks,
            "note": "Finite rational Laurent polynomials only; no Hahn-support proof."}


def valuation(q: Fraction, p: int) -> int:
    if not q:
        raise ValueError("This checker uses valuation only for nonzero rationals.")
    numerator, denominator = abs(q.numerator), q.denominator
    result = 0
    while numerator % p == 0:
        numerator //= p
        result += 1
    while denominator % p == 0:
        denominator //= p
        result -= 1
    return result


def residue(q: Fraction, modulus: int) -> int:
    """Residue of a rational with denominator coprime to the modulus."""
    return (q.numerator * pow(q.denominator, -1, modulus)) % modulus


def check_newton() -> dict[str, Any]:
    p = 7
    x = Fraction(3)
    records: list[dict[str, int]] = []
    # f(3)=7, f'(3)=6 is a 7-adic unit. Exact doubling follows from
    # f(x - f(x)/(2x)) = f(x)^2/(4x^2).
    for j in range(7):
        f = x*x - 2
        derivative = 2*x
        require(valuation(derivative, p) == 0, "Derivative ceased to be a unit.")
        require(valuation(f, p) == 2**j, "Residual valuation failed to double.")
        modulus = p ** min(2**j, 12)
        r = residue(x, modulus)
        require((r*r - 2) % modulus == 0, "Newton residue is not a root.")
        records.append({"iteration": j, "residual_valuation": valuation(f, p),
                        "checked_modulus": modulus, "root_residue": r})
        next_x = x - f / derivative
        require(next_x*next_x - 2 == f*f/(4*x*x), "Exact Newton identity failed.")
        require(valuation(next_x - x, p) == 2**j, "Correction valuation failed.")
        x = next_x
    return {"status": "PASS", "prime": p, "polynomial": "X^2 - 2",
            "seed": "3", "iterations_checked": len(records), "records": records}



def chinese_remainder(residues: tuple[int, ...], moduli: tuple[int, ...]) -> int:
    if len(residues) != len(moduli) or any(m < 2 for m in moduli):
        raise ValueError("Invalid Chinese remainder inputs.")
    if any(gcd(a, b) != 1 for i, a in enumerate(moduli) for b in moduli[:i]):
        raise ValueError("Moduli must be pairwise coprime.")
    modulus = prod(moduli)
    result = 0
    for r, m in zip(residues, moduli):
        partial = modulus // m
        result += r * partial * pow(partial, -1, m)
    return result % modulus


def check_profinite_finite_stages() -> dict[str, Any]:
    # Pair(n,j) = (n+j)^2+n is primitive recursive and injective.
    def pairing(n: int, j: int) -> int:
        return (n+j)**2 + n

    pairs = {pairing(n, j) for n in range(9) for j in range(65)}
    require(len(pairs) == 9*65, "Finite pairing injectivity check failed.")
    coherent_prefix_checks = bit_checks = 0
    for a in range(factorial(6)):
        residues = tuple(a % factorial(n) for n in range(1, 7))
        code = 0
        for n, r in enumerate(residues, start=1):
            require(factorial(n) < 2**(n*n), "Factorial bit bound failed.")
            for j in range(n*n):
                if (r >> j) & 1:
                    code |= 1 << pairing(n, j)
        decoded = {}
        for n in range(1, 7):
            value = sum(((code >> pairing(n, j)) & 1) << j for j in range(n*n))
            decoded[n] = value % factorial(n)
            require(decoded[n] == residues[n-1], "Factorial residue decoding failed.")
            bit_checks += 1
        for i in range(1, 7):
            for j in range(i, 7):
                require(decoded[j] % factorial(i) == decoded[i],
                        "Finite factorial coherence failed.")
                coherent_prefix_checks += 1
    # 8! = 2^7 * 3^2 * 5 * 7. Every 0/1 prime-coordinate pattern is
    # a finite idempotent, with multiplication = intersection.
    primes = (2, 3, 5, 7)
    moduli = (128, 9, 5, 7)
    modulus = factorial(8)
    require(prod(moduli) == modulus, "Factorization of 8! was wrong.")
    idempotents = {}
    local_recovery_checks = 0
    for bits in product((0, 1), repeat=4):
        e = chinese_remainder(bits, moduli)
        require((e*e-e) % modulus == 0, "Finite CRT point was not idempotent.")
        for i, p in enumerate(primes):
            require(e % p == bits[i], "Prime residue did not recover the bit.")
            local_recovery_checks += 1
        for n in range(1, 9):
            r = e % factorial(n)
            require((r*r-r) % factorial(n) == 0, "Factorial residue lost idempotence.")
        idempotents[bits] = e
    boolean_checks = 0
    for bits, e in idempotents.items():
        complement = tuple(1-b for b in bits)
        require((1-e) % modulus == idempotents[complement], "Complement identity failed.")
        boolean_checks += 1
        for other, f in idempotents.items():
            meet = tuple(b*c for b, c in zip(bits, other))
            require(e*f % modulus == idempotents[meet], "Intersection identity failed.")
            boolean_checks += 1
    return {"status": "PASS", "factorial_residue_samples": factorial(6),
            "decoded_residue_checks": bit_checks,
            "coherent_prefix_checks": coherent_prefix_checks,
            "idempotents_mod_8_factorial": len(idempotents),
            "prime_coordinate_recovery_checks": local_recovery_checks,
            "boolean_operation_checks": boolean_checks,
            "note": "Finite stages only; does not verify overspill or standard systems."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification.json"))
    args = parser.parse_args()
    report: dict[str, Any] = {
        "title": "Perfect Transcendence Gaps: exact finite regression checks",
        "scope": "Finite arithmetic only. Not a proof assistant or an infinitary certificate.",
        "status": "PASS",
        "checks": {},
    }
    try:
        report["checks"] = {
            "digit_recoding": check_digit_recoding(),
            "laurent_tails": check_laurent_tails(),
            "p_adic_newton": check_newton(),
            "profinite_finite_stages": check_profinite_finite_stages(),
        }
    except (ArithmeticError, ValueError, ZeroDivisionError) as exc:
        report["status"] = "FAIL"
        report["error"] = str(exc)
    try:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    except OSError as exc:
        print(f"Could not write verification report: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
