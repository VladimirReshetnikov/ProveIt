"""Reproduce the exact arithmetic checks and numerical summary.

Independent analytic targets are used where available. These checks are not
substitutes for universal proofs or for Lean elaboration.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from continuous_reference import (
    Formula, radius_problem, asymmetric_problem, dyadic, precision_for,
    example_ode, exp_enclosure, CQ, UNIT_SQUARE, clearance,
    segment_distance2, cauchy_sum, square_integral_enclosure,
)


def run():
    checks = 0
    def verify(condition, label):
        nonlocal checks
        if not condition:
            raise AssertionError(label)
        checks += 1

    for u in [F(0), F(1, 17), F(1), F(21, 16), F(21, 2), F(111, 7)]:
        k = precision_for(u)
        verify(2 ** k >= max(1, u), "precision bound")
        verify(k == 0 or 2 ** (k-1) < max(1, u), "precision minimality")

    logic_rows = []
    for name, formula, truth in [
        ("asymmetric minimum", asymmetric_problem(), F(1, 3)),
        ("interval radius", radius_problem(), F(1, 2)),
    ]:
        _, C = formula.weights()
        values = []
        for k in range(1, 7):
            value = formula.evaluate(k)
            bound = C * dyadic(k)
            verify(abs(value-truth) <= bound, "independent formula value")
            values.append((k, value))
            logic_rows.append(dict(problem=name, k=k, value=str(value),
                                   error=str(abs(value-truth)), bound=str(bound)))
        for k, a in values:
            for j, b in values:
                verify(abs(a-b) <= C * (dyadic(k)+dyadic(j)), "cross-mesh formula coherence")

    ode_rows, polygons = [], []
    exp_lo, exp_hi = exp_enclosure(F(1, 4))
    for n in range(9):
        poly, bound = example_ode(n)
        for j, x in enumerate(poly.nodes):
            verify(abs(x - 1) <= F(3, 4) * F(j, poly.N), "Euler tube invariant")
        endpoint = poly.nodes[-1]
        error_upper = max(abs(endpoint-exp_lo), abs(endpoint-exp_hi))
        verify(error_upper <= bound, "Euler independent exponential enclosure")
        verify(bound <= dyadic(n+3), "ODE output precision schedule")
        if polygons:
            previous, old_bound = polygons[-1]
            max_difference = max(abs(poly.value(F(j, 4*poly.N))
                                     - previous.value(F(j, 4*poly.N)))
                                 for j in range(poly.N+1))
            # Both polygons are affine on this common mesh: node maximum is uniform maximum.
            verify(max_difference <= bound+old_bound, "uniform Euler cross-mesh comparison")
        polygons.append((poly, bound))
        ode_rows.append(dict(n=n, N=poly.N, p=poly.p, endpoint=float(endpoint),
                             endpoint_rational=str(endpoint),
                             error_upper=float(error_upper), bound=float(bound),
                             bound_rational=str(bound)))

    verify(clearance(UNIT_SQUARE, CQ(0), F(1)), "sharp square clearance")
    verify(not clearance(UNIT_SQUARE, CQ(0), F(1001, 1000)), "reject excessive clearance")
    verify(not clearance(UNIT_SQUARE, CQ(1), F(1, 100)), "reject boundary query")
    verify(clearance(UNIT_SQUARE, CQ(2), F(1)), "outside query")
    verify(segment_distance2(CQ(3), CQ(3), CQ(1)) == 4, "degenerate edge distance")
    verify(segment_distance2(CQ(0), CQ(2), CQ(1, 1)) == 1, "interior quadratic minimum")
    verify(segment_distance2(CQ(0), CQ(2), CQ(-1, 1)) == 2, "clamped quadratic minimum")
    failed = False
    try:
        cauchy_sum(UNIT_SQUARE, CQ(1), F(1, 4), 4)
    except ValueError:
        failed = True
    verify(failed, "unguarded transform rejected")

    cauchy_rows = []
    imag_lo, imag_hi = square_integral_enclosure()
    for N in [4, 8, 16, 32, 64, 128]:
        q = cauchy_sum(UNIT_SQUARE, CQ(0), F(1), N)
        bound = F(64, N)  # ell=8, delta=1, M=1, K=0, eta=0.
        imag_error = max(abs(q.im-imag_lo), abs(q.im-imag_hi))
        norm2_upper = q.re*q.re + imag_error*imag_error
        verify(norm2_upper <= bound*bound, "Cauchy independent arctangent enclosure")
        verify(q.re == F(-4, N), "left-sum real part diagnostic")
        # A portable dyadic enclosure of the computed imaginary coordinate.
        scale = 1 << 40
        low = (q.im.numerator * scale) // q.im.denominator
        cauchy_rows.append(dict(N=N, real=float(q.re), imag=float(q.im),
                                imag_dyadic_lower=f"{low}/{scale}",
                                imag_dyadic_upper=f"{low+1}/{scale}",
                                error_upper=float(norm2_upper) ** 0.5,
                                bound=float(bound)))

    # Exact tests of the finite kernel identity underlying the Taylor proof.
    kernel_cases = 0
    for u in [CQ(1), CQ(1, 1), CQ(2, -1), CQ(-1, F(1, 2))]:
        for h in [CQ(F(1, 8)), CQ(0, F(1, 8)), CQ(F(-1, 8), F(1, 16))]:
            for m in range(8):
                value = sum(((h**r) / (u**(r+1)) for r in range(m)), CQ())
                remainder = (h**m) / ((u**m) * (u-h))
                verify((u-h).inverse() == value+remainder, "finite Cauchy kernel identity")
                kernel_cases += 1

    result = {
        "status": "passed", "exact_assertions": checks,
        "arithmetic": "fractions.Fraction; no floating-point pass/fail decisions",
        "scope": "Representative instances, independent analytic enclosures, guards, and finite identities. Not universal theorem verification.",
        "lean": "not run: no Lean executable was available",
        "logic": logic_rows, "ode": ode_rows, "cauchy": cauchy_rows,
        "kernel_identity_cases": kernel_cases,
    }
    target = Path(__file__).resolve().parents[1] / "validation" / "results.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "exact_assertions", "arithmetic", "lean")}))
    return result


if __name__ == "__main__":
    run()
