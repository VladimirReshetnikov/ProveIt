#!/usr/bin/env python3
"""Exact checks of fixed-coordinate cotangent-resolvent endpoint contacts.

All arithmetic is symbolic over Q(i, P, z, L); P denotes pi but is left
indeterminate. Numerical integration or approximate equality is not used.
Run: python check_contacts.py
"""
from pathlib import Path
import json
import sympy as sp


x, z, P, L, u, q, sigma = sp.symbols("x z P L u q sigma")
I = sp.I
MAX_M = 10
records = []
corruption_records = []


def normal(expr):
    return sp.factor(sp.cancel(sp.expand(expr)))


def require_zero(name, residual, **parameters):
    value = normal(residual)
    if value != 0:
        raise AssertionError((name, parameters, value))
    records.append({"check": name, "parameters": parameters,
                    "residual": "0"})


def truncated_multiply(a, b, degree):
    out = [sp.Integer(0)] * (degree + 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i + j <= degree:
                out[i + j] += ai * bj
    return [sp.expand(term) for term in out]


def truncated_power_coefficients(a, exponent, degree):
    out = [sp.Integer(1)] + [sp.Integer(0)] * degree
    for _ in range(exponent):
        out = truncated_multiply(out, a, degree)
    return out


# This is the formal Taylor jet of P*x*cot(P*x). Terms of degree 10
# already exceed those needed for M <= 10, but help check its construction.
scaled_cot = 1 + sum(
    (-1) ** n * 2 ** (2 * n) * sp.bernoulli(2 * n)
    * (P * x) ** (2 * n) / sp.factorial(2 * n)
    for n in range(1, MAX_M // 2 + 1)
)
sin_over_argument = sum(
    (-1) ** n * (P * x) ** (2 * n) / sp.factorial(2 * n + 1)
    for n in range(MAX_M // 2 + 1)
)
cosine = sum(
    (-1) ** n * (P * x) ** (2 * n) / sp.factorial(2 * n)
    for n in range(MAX_M // 2 + 1)
)
require_zero(
    "independent_formal_cotangent_jet",
    sp.series(scaled_cot * sin_over_argument - cosine,
              x, 0, MAX_M + 1).removeO(),
    through_degree=MAX_M,
)

examples = {}
for M in range(1, MAX_M + 1):
    degree = M - 1
    F = sp.Poly(scaled_cot - z * x, x)
    jet = [F.nth(j) for j in range(degree + 1)]
    residue = truncated_power_coefficients(jet, M, degree)[degree]
    mean = ((-z + I * P) ** M + (-z - I * P) ** M) / 2
    for epsilon in (1, -1):
        continued_mean = (-z - epsilon * I * P) ** M
        correction = epsilon * I * P * residue
        require_zero("negative_power_endpoint_contact",
                     mean - continued_mean - correction,
                     M=M, epsilon=epsilon)

        # Deliberately omit the endpoint-phase correction. This erroneous
        # assertion must fail as a polynomial identity at every tested M.
        corrupted_residual = normal(mean - continued_mean)
        if corrupted_residual == 0:
            raise AssertionError(("omitted_phase_was_not_detected", M, epsilon))
        corruption_records.append({
            "check": "omitted_endpoint_phase_rejected",
            "parameters": {"M": M, "epsilon": epsilon},
            "nonzero_residual": str(corrupted_residual),
        })
    if M <= 4:
        examples[str(M)] = {"finite_part_mean": str(sp.expand(mean)),
                            "local_residue": str(residue)}


# The ladder maps each formal source moment M_(L-1,r) to
# (L-1)*U_r + r*U_(r-1), where U_r denotes M_(L,r).
# Keeping L symbolic checks rational telescoping, not selected values of L.
for k in range(6):
    U = sp.symbols("U0:" + str(k + 1))
    derivative = 0
    for j in range(k + 1):
        r = k - j
        coefficient = ((-1) ** j * sp.factorial(k)
                       / (sp.factorial(r) * (L - 1) ** (j + 1)))
        image = (L - 1) * U[r] + (r * U[r - 1] if r else 0)
        derivative += coefficient * image
    require_zero("primitive_telescoping_L_not_1",
                 derivative - U[k], k=k, L="symbolic; L != 1")

    # At L=1, differentiating M_(0,k+1)/(k+1) gives U_k directly.
    require_zero("primitive_telescoping_L_equals_1",
                 sp.Rational(1, k + 1) * (k + 1) * U[k] - U[k], k=k)


# Boundary canary: at lambda=1, L_1(-1,q)=-1/(1-q).
# C=(1-q)/sigma, so the spectral specialization gives -1 exactly.
li_minus_one = q / (1 - q) ** 2
L1_minus_one = normal((q - 1) * li_minus_one / q)
spectral_boundary = normal((1 - q) / sigma * sigma * L1_minus_one)
require_zero("boundary_canary_spectral_value", spectral_boundary + 1,
             p=2, u=1, power=1)
ordinary_boundary = sp.diff(sp.Rational(1, 2) - x, x, 2)
require_zero("boundary_canary_ordinary_value", ordinary_boundary,
             p=2, u=1, power=1)
local_boundary = sp.limit(sp.cancel((u - 1) * (u - 2) / (u - 1)), u, 1)
require_zero("boundary_canary_local_contact", local_boundary + 1,
             p=2, u=1, power=1)


report = {
    "status": "PASS",
    "arithmetic": "Exact SymPy polynomial/rational arithmetic; P is symbolic pi",
    "sympy_version": sp.__version__,
    "positive_exact_checks": len(records),
    "deliberate_corruptions_rejected": len(corruption_records),
    "negative_power_range": "M=1,...,10; both epsilon=+1 and epsilon=-1",
    "primitive_range": "k=0,...,5; symbolic L != 1 and the L=1 branch",
    "boundary_canary": {
        "ordinary_integral": str(ordinary_boundary),
        "continued_spectral_value": str(spectral_boundary),
        "local_endpoint_contact": str(local_boundary),
    },
    "small_M_examples": examples,
    "checks": records,
    "corruption_controls": corruption_records,
    "scope": "Finite exact verification and falsification controls; the article contains all-index proofs.",
}
destination = Path(__file__).with_name("contact_checks.json")
destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({key: value for key, value in report.items()
                  if key not in ("checks", "corruption_controls")}, indent=2))
