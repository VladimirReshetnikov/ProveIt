#!/usr/bin/env python3
"""Exact universal Euler enclosures for g[a,b] = Im Li[a,b](i,1).

For positive integers a,b,N, let f(n)=H_(2n)^(b)/(2n+1)^a and
D f(n)=f(n)-f(n+1).  The signed-kernel theorem proves d_0=0 and
-1<d_k=D^k f(0)<0 for k>=1.  Therefore, with
E_N=sum(k<N,d_k/2^(k+1)), one has the STRICT bounds

                     E_N - 2^(-N) < g[a,b] < E_N.

The implementation forms E_N with the equivalent binomial-tail formula,
using O(N) rational updates rather than a quadratic difference table.
The analytic theorem, not the finite self-tests, establishes the bounds
for all parameters.  Everything required for evaluation and verification
uses the Python standard library.

Examples:
    python universal_euler.py 4 1 400
    python universal_euler.py --self-test
The self-test never overwrites the receipt.  --write-receipt is an explicit
creation command: equal existing data are left untouched, and differing
existing data are never replaced.  The default runner does not use this mode.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path

RECEIPT_PATH = Path(__file__).resolve().parents[1] / "data" / "universal_euler_receipt.json"


def _positive_integer(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{name} must be a positive integer")


def _values(a: int, b: int, N: int) -> list[Fraction]:
    harmonic = Fraction(0)
    values = []
    for n in range(N):
        if n:
            harmonic += Fraction(1, (2 * n - 1) ** b) + Fraction(1, (2 * n) ** b)
        values.append(harmonic / (2 * n + 1) ** a)
    return values


@dataclass(frozen=True)
class EulerEnclosure:
    a: int
    b: int
    N: int
    lower: Fraction
    upper: Fraction

    @property
    def E_N(self) -> Fraction:
        return self.upper

    def to_json(self) -> dict:
        return {
            "quantity": "Im Li_{a,b}(i,1)",
            "a": self.a, "b": self.b, "N": self.N,
            "inequality": "lower < g_{a,b} < upper",
            "lower": str(self.lower), "upper": str(self.upper),
            "E_N": str(self.E_N), "width": str(self.upper - self.lower),
            "endpoint_encoding": "exact rational strings",
        }


def enclose_gaussian(a: int, b: int, N: int) -> EulerEnclosure:
    """Return strict rational bounds; their closed hull is also an enclosure."""
    for name, value in (("a", a), ("b", b), ("N", N)):
        _positive_integer(value, name)
    power = 1 << N
    tail, choose, total = power - 1, 1, Fraction(0)
    for n, value in enumerate(_values(a, b, N)):
        total += (-1 if n % 2 else 1) * tail * value
        choose = choose * (N - n) // (n + 1)
        tail -= choose
    assert tail == 0
    upper = total / power
    return EulerEnclosure(a, b, N, upper - Fraction(1, power), upper)


def euler_differences(a: int, b: int, N: int) -> list[Fraction]:
    """Independent quadratic difference-table implementation, for diagnostics."""
    for name, value in (("a", a), ("b", b), ("N", N)):
        _positive_integer(value, name)
    row = _values(a, b, N)
    differences = []
    while row:
        differences.append(row[0])
        row = [x - y for x, y in zip(row, row[1:])]
    return differences


def _atan_reciprocal_bounds(q: int, terms: int) -> tuple[Fraction, Fraction]:
    """Strict alternating-series endpoints for arctan(1/q), q>1."""
    partial = sum((Fraction((-1) ** n, (2 * n + 1) * q ** (2 * n + 1))
                   for n in range(terms)), Fraction(0))
    next_partial = partial + Fraction((-1) ** terms,
                                       (2 * terms + 1) * q ** (2 * terms + 1))
    return min(partial, next_partial), max(partial, next_partial)


def g11_reference_bounds(terms: int = 80) -> tuple[Fraction, Fraction]:
    """Independent strict bounds from g11=-pi*log(2)/8.

    Machin: pi=16 atan(1/5)-4 atan(1/239).  For log(2), the
    2*atanh(1/3) series has tail strictly below
    9/[4(2M+1)3^(2M+1)].  No Gaussian Euler value is used here.
    """
    _positive_integer(terms, "terms")
    a5, b5 = _atan_reciprocal_bounds(5, terms)
    a239, b239 = _atan_reciprocal_bounds(239, terms)
    pi_lower, pi_upper = 16 * a5 - 4 * b239, 16 * b5 - 4 * a239
    log_lower = 2 * sum((Fraction(1, (2 * n + 1) * 3 ** (2 * n + 1))
                         for n in range(terms)), Fraction(0))
    log_upper = log_lower + Fraction(9, 4 * (2 * terms + 1) * 3 ** (2 * terms + 1))
    assert 0 < pi_lower < pi_upper and 0 < log_lower < log_upper
    return -pi_upper * log_upper / 8, -pi_lower * log_lower / 8


def build_self_test_receipt() -> dict:
    """Compute deterministic exact checks; this function performs no file writes."""
    if not __debug__:
        raise RuntimeError("Self-tests require assertions; do not run with python -O.")
    ref_lower, ref_upper = g11_reference_bounds(80)
    cases = []
    for a, b, N in ((1, 1, 8), (1, 1, 32), (1, 1, 64),
                    (1, 3, 16), (2, 1, 16), (3, 2, 16)):
        enclosure = enclose_gaussian(a, b, N)
        differences = euler_differences(a, b, N)
        assert differences[0] == 0
        assert all(Fraction(-1) < d < 0 for d in differences[1:])
        direct = sum((d / (1 << (k + 1)) for k, d in enumerate(differences)),
                     Fraction(0))
        assert enclosure.E_N == direct
        case = enclosure.to_json()
        case["difference_sign_checks"] = N - 1
        case["weighted_formula_equals_difference_table"] = True
        if (a, b) == (1, 1):
            assert enclosure.lower < ref_lower < ref_upper < enclosure.upper
            case["independent_g11_interval_strictly_contained"] = True
        cases.append(case)
    return {
        "schema": "universal-gaussian-euler-v1",
        "theorem": "For all positive integer a,b,N: E_N-2^(-N) < g[a,b] < E_N.",
        "scope": "Finite checks validate implementation; they do not prove the universal theorem.",
        "reference": {"identity": "g[1,1] = -pi*log(2)/8", "terms_per_series": 80,
                      "method": "rational Machin arctangent and atanh(1/3) bounds",
                      "lower": str(ref_lower), "upper": str(ref_upper)},
        "cases": cases,
    }


def run_self_test(receipt_path: str | Path | None = None) -> dict:
    """Verify implementation and compare the saved receipt without modifying it."""
    path = RECEIPT_PATH if receipt_path is None else Path(receipt_path)
    computed = build_self_test_receipt()
    recorded = json.loads(path.read_text(encoding="utf-8"))
    if recorded != computed:
        raise AssertionError(f"Universal Euler receipt mismatch: {path}")
    return {
        "status": "PASS", "cases": len(computed["cases"]),
        "independent_g11_containment_checks": 3,
        "difference_sign_checks": sum(c["difference_sign_checks"] for c in computed["cases"]),
        "receipt_match": True, "receipt_modified": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("a", type=int, nargs="?", default=1)
    parser.add_argument("b", type=int, nargs="?", default=1)
    parser.add_argument("N", type=int, nargs="?", default=64)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--self-test", action="store_true")
    modes.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    if args.write_receipt:
        receipt = build_self_test_receipt()
        RECEIPT_PATH.parent.mkdir(parents=True, exist_ok=True)
        if RECEIPT_PATH.exists():
            recorded = json.loads(RECEIPT_PATH.read_text(encoding="utf-8"))
            if recorded != receipt:
                parser.error(f"Refusing to replace differing existing receipt: {RECEIPT_PATH}")
            result = {"status": "UNCHANGED", "receipt": str(RECEIPT_PATH)}
        else:
            with RECEIPT_PATH.open("x", encoding="utf-8") as stream:
                stream.write(json.dumps(receipt, indent=2) + "\n")
            result = {"status": "CREATED", "receipt": str(RECEIPT_PATH)}
    elif args.self_test:
        result = run_self_test()
    else:
        try:
            result = enclose_gaussian(args.a, args.b, args.N).to_json()
        except ValueError as error:
            parser.error(str(error))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
