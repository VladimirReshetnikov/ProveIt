"""Finite regression evidence for explicitly bounded analytic algorithms."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import random
from analytic_programs import (
    sqrt_bracket, bounded_isqrt, sincos_observation, trig_polynomial,
    poly_eval, partial, polynomial_bounds, implicit_data, implicit_observation,
    curve_bounds, polygon_length_bracket,
)


def run():
    counts = {}
    c = 0
    for A, B, n in product(range(21), range(1, 12), range(9)):
        q = Q(A, B)
        lo, hi = sqrt_bracket(q, n)
        assert lo >= 0 and lo * lo <= q < hi * hi
        assert hi - lo == Q(1, 2**n)
        finer, finer_hi = sqrt_bracket(q, n + 1)
        assert lo <= finer <= finer_hi <= hi
        c += 1
    counts["square_root_brackets_and_nesting"] = c

    for m in range(1000):
        j = bounded_isqrt(m)
        assert j * j <= m < (j + 1) ** 2
    counts["bounded_integer_roots"] = 1000

    c = 0
    for A, B, n in product(range(-9, 10), range(1, 5), range(5)):
        t = Q(A, B)
        (co, si), cert = sincos_observation(t, n)
        co2, si2 = trig_polynomial(t, cert["degree"] + 17)
        assert abs(co - co2) + abs(si - si2) <= cert["tail"]
        co3, si3 = trig_polynomial(-t, cert["degree"])
        assert co == co3 and si == -si3
        c += 1
    counts["trigonometric_tail_and_parity"] = c

    c = 0
    for s, t in product([Q(-2), Q(-1, 2), Q(0), Q(1, 3), Q(2)], repeat=2):
        M = max(1, int(abs(s) + abs(t)) + 1)
        N = 4 * M + 12
        a, b = trig_polynomial(s, N)
        c1, d = trig_polynomial(t, N)
        e, f = trig_polynomial(s + t, N)
        assert abs(a * c1 - b * d - e) + abs(a * d + b * c1 - f) <= Q(1, 2 ** (N - 4 * M))
        c += 1
    counts["finite_addition_law_tail"] = c

    rng = random.Random(20261122)
    c = 0
    for _ in range(500):
        dim = rng.choice([2, 3])
        poly = {tuple(rng.randrange(4) for _ in range(dim)): Q(rng.randrange(-5, 6), rng.randrange(1, 5)) for _ in range(6)}
        p = tuple(Q(rng.randrange(-4, 5), 2) for _ in range(dim))
        h = tuple(Q(rng.randrange(-4, 5), 4) for _ in range(dim))
        H, _, _ = polynomial_bounds(poly, 2)
        remainder = poly_eval(poly, tuple(a + b for a, b in zip(p, h))) - poly_eval(poly, p)
        remainder -= sum(poly_eval(partial(poly, i), p) * h[i] for i in range(dim))
        assert abs(remainder) <= H * max(map(abs, h)) ** 2
        c += 1
    counts["polynomial_remainder"] = c

    examples = [
        ({(2, 0): Q(1), (0, 2): Q(1), (0, 0): Q(-1)}, (Q(0), Q(1))),
        ({(3, 0): Q(-1), (0, 1): Q(1)}, (Q(0), Q(0))),
        ({(1, 1): Q(1), (0, 0): Q(-1)}, (Q(1), Q(1))),
        ({(2, 0, 0): Q(1), (0, 2, 0): Q(1), (0, 0, 2): Q(1), (0, 0, 0): Q(-1)}, (Q(0), Q(0), Q(1))),
    ]
    c = 0
    sample_receipts = []
    for poly, p in examples:
        data = implicit_data(poly, p)
        for offset in [Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)]:
            x = tuple(z + offset * data["a"] for z in p[:-1])
            old = None
            for n in range(12):
                out = implicit_observation(data, x, n)
                lo, hi, mid = out["lower"], out["upper"], out["midpoint"]
                assert poly_eval(data["poly"], x + (lo,)) <= 0 <= poly_eval(data["poly"], x + (hi,))
                assert hi - lo <= Q(1, 2 ** (n + 1))
                assert abs(poly_eval(data["poly"], x + (mid,))) <= data["B"] * (hi - lo)
                if old is not None:
                    assert old[0] <= lo <= hi <= old[1]
                old = lo, hi
                c += 1
        sample_receipts.append({"base": list(map(str, p)), "g": str(data["g"]), "r": str(data["r"]), "a": str(data["a"])})
    counts["implicit_function_brackets"] = c

    curves = [
        [[Q(0), Q(1)], [Q(0), Q(0), Q(1)]],
        [[Q(0), Q(0), Q(1)], [Q(0), Q(0), Q(0), Q(1)]],
        [[Q(1), Q(2)], [Q(-1), Q(3)], [Q(0), Q(1)]],
        [[Q(0)], [Q(0)]],
    ]
    c = 0
    for curve in curves:
        a, b = Q(-1), Q(1)
        V, K = curve_bounds(curve, a, b)
        for k in range(7):
            lo, hi = polygon_length_bracket(curve, a, b, k, 28)
            flo, fhi = polygon_length_bracket(curve, a, b, k + 1, 28)
            assert lo <= V * (b - a)
            # Intervals, rather than floats, account for root errors.
            assert hi >= flo - 2 * K * (b - a) ** 2 / 2**k
            assert fhi >= lo
            c += 1
    counts["polygon_length_refinement_brackets"] = c

    invalid = 0
    for action in [lambda: sqrt_bracket(Q(-1), 3), lambda: implicit_data({(2, 0): Q(1), (0, 2): Q(1)}, (Q(0), Q(0))), lambda: sincos_observation(Q(3), 2, 1)]:
        try:
            action()
        except ValueError:
            invalid += 1
        else:
            raise AssertionError("invalid input was accepted")
    counts["invalid_domain_rejections"] = invalid
    result = {"status": "PASS", "kind": "finite exact-rational regression checks; not formal proofs", "counts": counts, "total_checks": sum(counts.values()), "implicit_examples": sample_receipts}
    out = Path(__file__).resolve().parents[1] / "artifacts" / "analytic_checks.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
