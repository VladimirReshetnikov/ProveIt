#!/usr/bin/env python3
"""Exact rational checks for the constructive Hilbert solver in the report.

Two examples are included:
* an infinite diagonal ell^2 equation, with an actual finite truncation of b;
* the variable-coefficient weak equation -((1+x)u')'=1 on [0,1], with
  zero boundary values, represented by rational zero-boundary polynomials.

The evidence is diagnostic.  General correctness, residual certification,
coercivity, and the error-to-uniform-norm implication are proved in the report.
No floating-point value is used to pass a check; decimal values are summaries.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
from typing import Iterable


def dyadic(n: int) -> Q:
    if n < 0:
        raise ValueError("negative precision")
    return Q(1, 1 << n)


def ceiling(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def solver_parameters(m: Q, M: Q, B: Q, n: int) -> dict:
    if not (0 < m <= M and B >= 0 and n >= 0):
        raise ValueError("Require 0 < m <= M, B >= 0, and n >= 0")
    lam = m / (M * M)
    delta = m * m / (2 * M * M)
    q = 1 - delta
    h = ceiling(1 / delta)
    R = max(1, ceiling(lam * B / delta))
    C = max(1, ceiling(2 * lam / delta))
    k = n + 3 + C
    N = h * (n + R + 3)
    eta = delta * dyadic(n + 3)
    assert h * delta >= 1
    assert R * q**N <= dyadic(n + 3)
    assert 2 * lam * dyadic(k) <= eta
    return dict(m=m, M=M, B=B, lam=lam, delta=delta, q=q,
                h=h, R=R, C=C, k=k, N=N, eta=eta)


def ratio_summary(x: Q) -> dict:
    """Give a compact exact dyadic upper bound, retaining a hash of the ratio."""
    if x < 0:
        raise ValueError("nonnegative quantity expected")
    exact = f"{x.numerator}/{x.denominator}"
    if x == 0:
        upper = Q(0)
    else:
        # Start within one bit of floor(log2(denominator/numerator)); refine
        # using exact integer comparisons.  No real logarithm is evaluated.
        exponent = x.denominator.bit_length() - x.numerator.bit_length()
        upper = Q(1, 1 << exponent) if exponent >= 0 else Q(1 << (-exponent))
        while upper < x:
            upper *= 2
        while upper / 2 >= x:
            upper /= 2
    assert x <= upper
    return {"decimal": float(x), "verified_rational_upper_bound": str(upper),
            "numerator_bits": x.numerator.bit_length(),
            "denominator_bits": x.denominator.bit_length(),
            "exact_ratio_sha256": sha256(exact.encode()).hexdigest()}


# ---------- Finite-support rational vectors ----------

Vector = tuple[Q, ...]


def norm_squared(v: Vector) -> Q:
    return sum((x * x for x in v), Q(0))


def vector_difference(v: Vector, w: Vector) -> Vector:
    return tuple((v[i] if i < len(v) else Q(0)) -
                 (w[i] if i < len(w) else Q(0))
                 for i in range(max(len(v), len(w))))


def diagonal_A(v: Vector) -> Vector:
    return tuple((1 + Q(1, i + 1)) * x for i, x in enumerate(v))


def diagonal_rhs(k: int) -> Vector:
    # The omitted squared norm is exactly 4**(-k)/3 <= 4**(-k).
    return tuple(dyadic(i + 1) for i in range(k))


def diagonal_run(n: int) -> tuple[Vector, dict]:
    p = solver_parameters(Q(1), Q(2), Q(1), n)
    b = diagonal_rhs(p["k"])
    z = (Q(0),) * p["k"]
    for _ in range(p["N"]):
        az = diagonal_A(z)
        z = tuple(x - p["lam"] * ax + p["lam"] * bi
                  for x, ax, bi in zip(z, az, b))
    # An independent scalar closed form checks the actual finite recurrence.
    for i, zi in enumerate(z):
        ai = 1 + Q(1, i + 1)
        ui = Q(i + 1, i + 2) * dyadic(i + 1)
        assert zi == ui * (1 - (1 - p["lam"] * ai) ** p["N"])

    head_error = sum(((zi - Q(i + 1, i + 2) * dyadic(i + 1)) ** 2
                      for i, zi in enumerate(z)), Q(0))
    tail_upper = Q(1, 3 * (1 << (2 * p["k"])))
    solution_error_upper = head_error + tail_upper
    # Residual tail has the exact geometric sum because the output vector
    # vanishes there and its residual is -b_i.
    az = diagonal_A(z)
    residual_squared = norm_squared(tuple(ax - bi for ax, bi in zip(az, b))) + tail_upper
    target_squared = dyadic(2 * n + 4)
    assert solution_error_upper <= target_squared
    assert residual_squared <= target_squared
    assert norm_squared(z) <= Q(1)
    return z, {
        "precision_n": n, "operator": "A_i = 1 + 1/(i+1)",
        "rhs": "b_i = 2^(-i-1)", "solution": "u_i = (i+1)/(i+2) * 2^(-i-1)",
        "iteration_count": p["N"], "input_precision_k": p["k"],
        "support_length": len(z), "actual_perturbation": "truncate b to i < k; A exact",
        "rhs_tail_squared_exact": str(tail_upper),
        "solution_error_squared_upper": ratio_summary(solution_error_upper),
        "residual_squared": ratio_summary(residual_squared),
        "required_error_squared_bound": str(target_squared),
        "solution_error_check": True, "residual_error_check": True,
        "closed_form_agreement": True,
    }


# ---------- Rational polynomial operations ----------

Poly = tuple[Q, ...]  # ascending coefficients; zero has the single coefficient 0
ZERO: Poly = (Q(0),)
X: Poly = (Q(0), Q(1))
ONE: Poly = (Q(1),)


def polynomial(coefficients: Iterable[Q]) -> Poly:
    p = list(map(Q, coefficients)) or [Q(0)]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def padd(p: Poly, q: Poly) -> Poly:
    return polynomial((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                      for i in range(max(len(p), len(q))))


def pscale(a: Q, p: Poly) -> Poly:
    return polynomial(a * c for c in p)


def psub(p: Poly, q: Poly) -> Poly:
    return padd(p, pscale(Q(-1), q))


def pmul(p: Poly, q: Poly) -> Poly:
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        for j, qj in enumerate(q):
            out[i + j] += pi * qj
    return polynomial(out)


def pderivative(p: Poly) -> Poly:
    return polynomial(i * p[i] for i in range(1, len(p)))


def pantiderivative(p: Poly) -> Poly:
    return polynomial([Q(0)] + [c / (i + 1) for i, c in enumerate(p)])


def pintegral(p: Poly) -> Q:
    return sum((c / (i + 1) for i, c in enumerate(p)), Q(0))


def pevaluate(p: Poly, x: Q) -> Q:
    value = Q(0)
    for coefficient in reversed(p):
        value = x * value + coefficient
    return value


def inner_l2(p: Poly, q: Poly) -> Q:
    return pintegral(pmul(p, q))


def inner_energy(p: Poly, q: Poly) -> Q:
    return inner_l2(pderivative(p), pderivative(q))


def zero_boundary(p: Poly) -> bool:
    return pevaluate(p, Q(0)) == 0 and pevaluate(p, Q(1)) == 0


def pde_operator(v: Poly) -> Poly:
    """(Av)'=(1+x)*v' - integral((1+x)*v'), (Av)(0)=0."""
    if not zero_boundary(v):
        raise ValueError("The energy-space polynomial must vanish at both endpoints")
    g = pmul((Q(1), Q(1)), pderivative(v))
    derivative = psub(g, (pintegral(g),))
    result = pantiderivative(derivative)
    assert zero_boundary(result)
    return result


def green_operator(f: Poly) -> Poly:
    """Exact polynomial Green operator with -G(f)''=f and zero endpoints."""
    twice_integrated = pantiderivative(pantiderivative(f))
    result = psub(pscale(pevaluate(twice_integrated, Q(1)), X), twice_integrated)
    assert zero_boundary(result)
    assert pscale(Q(-1), pderivative(pderivative(result))) == f
    return result


def polynomial_identity_checks() -> dict:
    v = (Q(0), Q(1), Q(-1))             # x(1-x)
    w = (Q(0), Q(0), Q(1), Q(-1))      # x^2(1-x)
    t = pmul(v, (Q(1), Q(-2)))         # x(1-x)(1-2x)
    samples = [v, w, t, psub(v, pscale(Q(3, 2), w))]
    a = (Q(1), Q(1))
    checks = 0
    for p in samples:
        ap = pde_operator(p)
        assert zero_boundary(ap)
        assert inner_energy(p, p) >= inner_l2(p, p) >= 0
        assert inner_energy(ap, p) >= inner_energy(p, p)
        assert inner_energy(ap, ap) <= 4 * inner_energy(p, p)
        for q in samples:
            assert inner_energy(ap, q) == pintegral(pmul(a, pmul(pderivative(p), pderivative(q))))
            assert inner_energy(ap, q) == inner_energy(p, pde_operator(q))
            checks += 2
    for f in [ONE, a, (Q(1), Q(-2), Q(3))]:
        gf = green_operator(f)
        assert inner_energy(gf, gf) <= inner_l2(f, f)
        for v0 in samples:
            assert inner_energy(gf, v0) == inner_l2(f, v0)
            checks += 1
    return {"exact_identity_comparisons": checks,
            "coercivity_and_norm_samples": len(samples),
            "green_operator_samples": 3,
            "scope": "finite exact examples of the report's identities"}


def pde_run(n: int) -> tuple[Poly, dict]:
    p = solver_parameters(Q(1), Q(2), Q(1), n)
    b = green_operator(ONE)
    assert b == (Q(0), Q(1, 2), Q(-1, 2))
    z = ZERO
    for _ in range(p["N"]):
        z = padd(psub(z, pscale(p["lam"], pde_operator(z))), pscale(p["lam"], b))
        assert zero_boundary(z)
    residual = psub(pde_operator(z), b)
    residual_squared = inner_energy(residual, residual)
    target_squared = dyadic(2 * n + 4)
    assert 0 <= residual_squared <= target_squared
    assert len(z) - 1 <= p["N"] + 1
    # Since m=1, the proved residual estimate yields energy error at most the
    # residual norm.  The proved energy-to-uniform inequality gives the same
    # bound uniformly on the interval.
    return z, {
        "precision_n": n, "iteration_count": p["N"],
        "polynomial_degree": len(z) - 1,
        "left_endpoint_exact": str(pevaluate(z, Q(0))),
        "right_endpoint_exact": str(pevaluate(z, Q(1))),
        "residual_energy_squared": ratio_summary(residual_squared),
        "required_error_squared_bound": str(target_squared),
        "exact_residual_comparison": True,
        "certified_energy_error_bound": str(dyadic(n + 2)),
        "certified_uniform_error_bound": str(dyadic(n + 2)),
        "certificate_dependency": "report coercivity residual bound, m=1; energy dominates sup norm",
        "logarithm_evaluations": 0,
    }


def run_checks(pde_max_n: int = 3) -> dict:
    params = solver_parameters(Q(1), Q(2), Q(1), 0)
    diagonal_outputs, diagonal_rows = [], []
    for n in range(7):
        output, row = diagonal_run(n)
        diagonal_outputs.append(output)
        diagonal_rows.append(row)
    pairwise = 0
    for n, v in enumerate(diagonal_outputs):
        for ell in range(n, len(diagonal_outputs)):
            distance_squared = norm_squared(vector_difference(v, diagonal_outputs[ell]))
            assert distance_squared <= dyadic(2 * n + 2)
            pairwise += 1
    identities = polynomial_identity_checks()
    pde_outputs, pde_rows = [], []
    for n in range(pde_max_n + 1):
        output, row = pde_run(n)
        pde_outputs.append(output)
        pde_rows.append(row)
    pde_pairwise = 0
    for n, v in enumerate(pde_outputs):
        for ell in range(n, len(pde_outputs)):
            difference = psub(v, pde_outputs[ell])
            assert inner_energy(difference, difference) <= dyadic(2 * n + 2)
            pde_pairwise += 1
    return {
        "status": "passed",
        "arithmetic": "Python fractions.Fraction; every pass/fail comparison exact",
        "scope": "finite computational diagnostics, not machine-checked iPRA derivations",
        "parameters": {key: str(params[key]) for key in
                       ("m", "M", "B", "lam", "delta", "q", "h", "R", "C")},
        "clock": "k_n=n+7; N_n=8(n+5)",
        "diagonal_ell2": diagonal_rows,
        "diagonal_pairwise_regularity_checks": pairwise,
        "polynomial_identities": identities,
        "pde": pde_rows,
        "pde_pairwise_regularity_checks": pde_pairwise,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--pde-max-n", type=int, default=3)
    args = parser.parse_args()
    result = run_checks(args.pde_max_n)
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(data)
    print(json.dumps({"status": result["status"],
                      "diagonal_precisions": len(result["diagonal_ell2"]),
                      "pde_precisions": len(result["pde"]),
                      "largest_pde_degree": max(r["polynomial_degree"] for r in result["pde"]),
                      "exact_identity_comparisons": result["polynomial_identities"]["exact_identity_comparisons"],
                      "pairwise_regularity_checks": result["diagonal_pairwise_regularity_checks"] +
                                                     result["pde_pairwise_regularity_checks"]}, indent=2))
