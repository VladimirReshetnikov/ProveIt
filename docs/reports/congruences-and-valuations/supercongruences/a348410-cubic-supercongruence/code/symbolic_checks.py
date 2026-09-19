#!/usr/bin/env python3
"""Optional exact polynomial certificates. Requires SymPy (tested with 1.14.0)."""
from pathlib import Path
import json
import sympy as s


def main() -> None:
    y, t, A, u, v, i, n = s.symbols("y t A u v i n")
    q = y * (1 - y) ** 2 * (1 + y)
    numerator = 1 - y ** 2
    denominator = 1 - y - 4 * y ** 2
    P = ((256 * t ** 2 + 107 * t - 32) * (A ** 4 - A ** 3)
         + (96 * t ** 2 + 36 * t) * A ** 2
         - (16 * t ** 2 + 4 * t) * A + t ** 2)
    certificate = s.cancel(denominator ** 4
                           * P.subs({t: q, A: numerator / denominator}))
    if certificate != 0:
        raise AssertionError("The substituted quartic is not identically zero")
    resultant = s.factor(s.resultant(q - t, A * denominator - numerator, y))
    ratio = s.cancel(resultant / P)
    if ratio.free_symbols or ratio == 0:
        raise AssertionError("The resultant is not a nonzero constant times P")
    # Both parity weights used in the key lemma are exact polynomial identities.
    odd_weight = s.expand((u + v) * (u - v))
    even_plus = s.expand((u + v) ** 2)
    even_minus = s.expand((u - v) ** 2)
    if odd_weight != u ** 2 - v ** 2:
        raise AssertionError("Odd parity weight")
    if even_plus != u ** 2 + 2 * u * v + v ** 2:
        raise AssertionError("Even parity weight +")
    if even_minus != u ** 2 - 2 * u * v + v ** 2:
        raise AssertionError("Even parity weight -")
    result = {"sympy": s.__version__, "quartic_substitution_residual": str(certificate),
              "resultant_divided_by_P": str(ratio), "parity_polynomial_identities": "PASS",
              "result": "PASS: all symbolic polynomial identities succeeded"}
    output = Path(__file__).resolve().parents[1] / "data" / "symbolic_verification.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
