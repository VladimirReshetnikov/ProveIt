#!/usr/bin/env python3
"""Exact checks of the finite polynomial-adic norm certificate.

SymPy supplies exact polynomial arithmetic and an independently computed
resultant.  These finite checks do not replace the universal human proof.
"""
from pathlib import Path
import json
import sympy as S

x, y = S.symbols("x y")


def check_case(m, f_expr, rows, modulus=None):
    opts = {"modulus": modulus} if modulus is not None else {"domain": S.QQ}
    poly = lambda expr: S.Poly(expr, x, **opts)
    f = poly(f_expr)
    assert f.degree() >= 1
    assert S.gcd(f, f.diff()).degree() == 0  # Automatic separable case.
    normalized_rows = [poly(a) for a in rows]
    data = []
    for j, aj in enumerate(normalized_rows):
        if aj.is_zero:
            continue
        b, a = aj, 0
        for _ in range(aj.degree() + 1):
            q, r = b.div(f)
            if not r.is_zero:
                break
            a, b = a + 1, q
        else:
            raise AssertionError("Degree bound did not terminate division")
        assert not b.rem(f).is_zero
        assert aj == f ** a * b
        data.append((m * a + j, j, a, b))
    assert data
    s, k, a, b = min(data, key=lambda item: item[0])
    assert sum(weight == s for weight, *_ in data) == 1
    g_expr = sum(aj.as_expr() * y ** j for j, aj in enumerate(normalized_rows))
    n_expr = S.resultant(y ** m - f.as_expr(), g_expr, y)
    norm = poly(n_expr)
    h, rem = norm.div(f ** s)
    assert rem.is_zero
    predicted = (poly((-1) ** (k * (m - 1))) * b ** m).rem(f)
    actual = h.rem(f)
    assert actual == predicted and not actual.is_zero
    cap = max(m * aj.degree() + j * f.degree()
              for j, aj in enumerate(normalized_rows) if not aj.is_zero)
    assert not norm.is_zero and norm.degree() <= cap
    assert s * f.degree() <= cap
    assert h.degree() <= cap - s * f.degree()
    return {"m": m, "field": f"F_{modulus}" if modulus else "Q",
            "f": str(f.as_expr()), "rows": [str(a.as_expr()) for a in normalized_rows],
            "selected_index": k, "selected_order": a, "norm_f_order": s,
            "norm_degree": norm.degree(), "degree_cap": cap,
            "nonzero_residue": str(actual.as_expr())}


def main():
    records = []
    for f in [x ** 2 - 1, x ** 4 + 1, x ** 3 - x + 1]:
        for m in range(1, 5):
            for shift in [0, 2]:
                rows = [f ** (shift + ((j + 1) % m)) * (x + j + 1)
                        for j in range(m)]
                records.append(check_case(m, f, rows))
    records.append(check_case(2, x ** 4 + 1, [-x ** 2, 1]))
    records.append(check_case(2, x ** 2 - 1, [x - 1, 1]))
    records.append(check_case(2, x ** 3 + x + 1, [x + 1, 1], modulus=2))
    records.append(check_case(3, x ** 6 + x + 1, [x ** 4, 1, x], modulus=3))
    records.append(check_case(3, x ** 2 + 1,
                              [(x ** 2 + 1) ** 2, x, 1], modulus=3))
    out = {"status": "passed", "cases": len(records), "arithmetic": "exact SymPy QQ and prime fields",
           "records": records, "proof_status": "Finite certificate checks; universal human proof supplied separately."}
    destination = Path(__file__).resolve().parents[1] / "validation" / "adic_norm_validation.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "cases": len(records), "report": str(destination)}))


if __name__ == "__main__":
    main()
