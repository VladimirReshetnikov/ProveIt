"""Exact and numerical validation of the joint coefficient expansion.

The identities are proved in the article. These checks compare independent
finite formulas and direct Fourier quadrature, without certifying analytic
remainders or global branch geometry.
"""
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling


def exp_coefficients(log_coefficients, degree):
    """Exponential Taylor coefficients via the differential equation E'=L'E."""
    out = [sp.Integer(1)]
    for n in range(1, degree + 1):
        out.append(sp.expand(sum(
            k * log_coefficients.get(k, 0) * out[n - k]
            for k in range(1, n + 1)
        ) / n))
    return out


def mul_coefficients(left, right, degree):
    return [sp.expand(sum(left[k] * right[n - k] for k in range(n + 1)))
            for n in range(degree + 1)]


def half_polygamma(order, integer_part, gamma, log2):
    """Exact psi^(order)(integer_part+1/2), using recurrence from 1/2."""
    if order == 0:
        return -gamma - 2 * log2 + sum(
            sp.Rational(2, 2 * k + 1) for k in range(integer_part)
        )
    exponent = order + 1
    tail = (2 ** exponent - 1) * sp.zeta(exponent)
    tail -= sum(sp.Rational(2, 2 * k + 1) ** exponent
                for k in range(integer_part))
    return sp.expand((-1) ** (order + 1) * sp.factorial(order) * tail)


degree = 5
epsilon, q, v, z = sp.symbols("epsilon q v z")
gamma, log2, centered = sp.symbols("gamma log2 C", real=True)

# Route 1: expand the exponential by its differential equation, with a
# bookkeeping variable giving q and epsilon total degree one.
log_coefficients = {
    n: -q * v ** 2 * epsilon ** (n - 1) * z ** n / (2 * sp.factorial(n))
    for n in range(1, degree + 1)
}
direct = exp_coefficients(log_coefficients, degree)
stirling_checks = []
for n in range(degree + 1):
    predicted = sp.Integer(1) if n == 0 else sum(
        stirling(n, k, kind=2) * (-q * v ** 2 / 2) ** k
        * epsilon ** (n - k) * z ** n / sp.factorial(n)
        for k in range(1, n + 1)
    )
    residual = sp.expand(direct[n] - predicted)
    assert residual == 0, (n, residual)
    stirling_checks.append({"total_degree": n, "exact_residual": "0"})

# Central kernel jets by the reciprocal-Gamma formula:
# H_(2k+delta)(0)/g(0) = 2^k exp(delta log2/2)
#       prod_{r=1}^k(1/2-r-delta/2) sqrt(pi)/Gamma(1/2-delta/2).
delta, w = sp.symbols("delta w")
base_log = {
    n: -half_polygamma(n - 1, 0, gamma, log2)
       * (-sp.Rational(1, 2)) ** n / sp.factorial(n)
    for n in range(1, degree + 1)
}
base_log[1] += log2 / 2
base_exp = exp_coefficients(base_log, degree)
central_checks = []
marginal_checks = []
marginal_values = {}

for k in range(degree + 1):
    product = sp.Poly(sp.prod(sp.Rational(1, 2) - r - delta / 2
                              for r in range(1, k + 1)), delta)
    polynomial = [product.nth(n) for n in range(degree + 1)]
    reciprocal_jets = [sp.expand(2 ** k * value)
                       for value in mul_coefficients(polynomial, base_exp, degree)]

    # Route 2: positive-half-integer Gamma moments, then reflection.
    positive_log = {
        n: half_polygamma(n - 1, k, gamma, log2) / sp.factorial(n)
        for n in range(1, degree + 1)
    }
    positive_log[1] += log2
    gamma_exp = exp_coefficients(positive_log, degree)
    cos_coefficients = [sp.Integer(0)] * (degree + 1)
    for n in range(0, degree + 1, 2):
        cos_coefficients[n] = (-1) ** (n // 2) * sp.pi ** n / sp.factorial(n)
    moment_coefficients = mul_coefficients(gamma_exp, cos_coefficients, degree)
    gamma_ratio = sp.factorial(2 * k) / (4 ** k * sp.factorial(k))

    for j in range(degree + 1):
        lhs = sp.expand(sp.factorial(j) * reciprocal_jets[j])
        rhs = sp.expand((-1) ** k * sp.Rational(2) ** (k - j)
                        * sp.factorial(j) * gamma_ratio * moment_coefficients[j])
        residual = sp.expand(lhs - rhs)
        assert residual == 0, (k, j, residual)
        central_checks.append({"k": k, "derivative_order": j,
                               "exact_residual": "0"})

    if k <= 4:
        # D_k=(-1)^k H^(k)_(2k)(0)/(k! g(0)).
        # Q_k(-log2) is the coefficient of w^k in
        # Gamma(k+1/2+w)/sqrt(pi) exp(log2*w) cos(pi*w).
        d_k = sp.expand((-1) ** k * reciprocal_jets[k])
        q_k = sp.expand(gamma_ratio * moment_coefficients[k])
        residual = sp.expand(d_k - q_k)
        assert residual == 0, (k, residual)
        marginal_checks.append({"j": k, "exact_residual": "0"})
        compact = sp.expand(d_k.subs(gamma, centered - log2))
        assert not compact.has(log2)
        marginal_values[str(k)] = {
            "definition_of_C": "EulerGamma + log(2)",
            "exact_polynomial": str(compact),
        }

# Independent real Fourier quadrature versus the parabolic-cylinder formula.
mp.mp.dps = 80
kernel_checks = []
for alpha in map(mp.mpf, ("0.3", "1.2", "2.4")):
    for xi in map(mp.mpf, ("-1", "0", "1")):
        def integrand(t):
            return mp.exp(-t * t / 2) * t ** alpha * mp.cos(t * xi + mp.pi * alpha / 2)

        quadrature = mp.quad(integrand, [0, 1, 3, 7, mp.inf]) / mp.pi
        closed = mp.exp(-xi * xi / 4) * mp.pcfd(alpha, -xi) / mp.sqrt(2 * mp.pi)
        error = abs(quadrature - closed)
        assert error < mp.mpf("1e-65"), (alpha, xi, error)
        kernel_checks.append({
            "alpha": str(alpha), "xi": str(xi),
            "fourier_quadrature": mp.nstr(quadrature, 40),
            "parabolic_cylinder": mp.nstr(closed, 40),
            "absolute_error": mp.nstr(error, 8),
        })

result = {
    "status": "PASS",
    "scope": "Exact finite identities and nonrigorous high-precision Fourier diagnostics.",
    "versions": {"sympy": sp.__version__, "mpmath": mp.__version__},
    "stirling_expansion_degree": degree,
    "stirling_expansion_checks": stirling_checks,
    "central_gamma_checks": central_checks,
    "marginal_identity_checks": marginal_checks,
    "marginal_coefficients": marginal_values,
    "kernel_precision_dps": mp.mp.dps,
    "kernel_closed_form_checks": kernel_checks,
}
destination = Path(__file__).resolve().parent.parent / "data" / "symbolic_validation.json"
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({
    "status": result["status"],
    "stirling_checks": len(stirling_checks),
    "central_gamma_checks": len(central_checks),
    "marginal_checks": len(marginal_checks),
    "kernel_checks": len(kernel_checks),
    "marginal_coefficients": marginal_values,
}, indent=2))
