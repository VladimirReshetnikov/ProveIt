#!/usr/bin/env python3
"""Reproduce the finite checks accompanying the level-7 A279619 article.

Run with Python 3.10+ and the pinned requirements.txt; no network is used.
All paths are relative to the caller unless --output specifies otherwise.

Exact arithmetic verifies finite coefficient identities. High-precision
floating-point identities and residuals are corroborating computations, not
proofs, interval certificates, effective remainder bounds, or certified
integer-threshold enclosures. The article supplies the analytic arguments.

Notation: G = Gamma(1/7) Gamma(2/7) Gamma(4/7), A0 = 3G/(8*pi**2),
C = sqrt(3*pi)/G, B = -2*sqrt(pi)*C, q0 = (B/A0)**2.
The symbol q0 below is a CM constant, not the modular nome exp(2*pi*i*tau).

Prior work: L. A. O'Brien, Modular forms and two new integer sequences at
level 7 (2016), gives the recurrence and modular parametrization. The k=2
member is the established sequence A183204. Its asymptotic result is due
to M. D. Hirschhorn, A sequence considered by Shaun Cooper, New Zealand
J. Math. 43 (2013), 37-42; see also S. Cooper (2025), Section 10.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
import time
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp

R = sp.Rational
ZERO = sp.S.Zero
ONE = sp.S.One


def require(condition, message):
    """Do not disable verification when Python is invoked with -O."""
    if not condition:
        raise ArithmeticError(message)


def mul(a, b, order):
    """Truncated ordinary power-series product (exact or symbolic)."""
    return [sp.expand(sum(a[j] * b[n-j]
                         for j in range(max(0, n-len(b)+1), min(n+1, len(a)))))
            for n in range(order+1)]


def power(a, exponent, order):
    """Coefficients of a(t)**exponent when a[0]=1, at any fixed order.

    The recurrence follows from a H' = exponent*a' H and works for a
    symbolic exponent. No infinite symbolic expansion is requested.
    """
    require(a[0] == 1, "power-series constant term must be one")
    result = [ONE]
    for n in range(1, order+1):
        result.append(sp.expand(sum(((exponent+1)*j-n) * a[j] * result[n-j]
                                    for j in range(1, min(n+1, len(a)))) / n))
    return result


def log_series(a, order):
    """Coefficients ell_j of log(sum a_j*t**j), with a_0=1."""
    require(a[0] == 1, "log-series constant term must be one")
    result = [ZERO]
    for n in range(1, order+1):
        result.append(sp.expand(a[n] - sum(j*result[j]*a[n-j]
                                          for j in range(1, n))/n))
    return result


def frobenius(exponent, order):
    """Exact even/odd Frobenius generator at t=1-27x."""
    exponent = sp.sympify(exponent)
    f = [ONE]
    for j in range(1, order+1):
        v = exponent+j
        f.append(sp.cancel(((29*(v-1)**2+14*(v-1)+R(20, 9))*f[-1]
                            -(v-R(4, 3))*(v-R(5, 3))*(f[-2] if j >= 2 else 0))
                           / (14*v*(2*v-1))))
    return f


def check_ode_and_frobenius(even, odd, order):
    x, t, r = sp.symbols("x t r")
    original = [x*(1-26*x-27*x*x), 1-39*x-54*x*x, -2*(1+3*x)]
    transformed = [sp.expand((729*original[0]).subs(x, (1-t)/27)),
                   sp.expand((-27*original[1]).subs(x, (1-t)/27)),
                   sp.expand(original[2].subs(x, (1-t)/27))]
    require(transformed == [28*t-29*t*t+t**3, 14-43*t+2*t*t,
                            R(-20, 9)+R(2, 9)*t], "ODE change of variables")
    indicial = sp.factor(28*r*(r-1)+14*r)
    require(indicial == 14*r*(2*r-1), "indicial polynomial")
    for exponent, coefficients in [(ZERO, even), (R(1, 2), odd)]:
        h = sum(c*t**j for j, c in enumerate(coefficients))
        # This is t**(1-r) times the differential operator on t**r*h.
        residual = sp.expand(
            (28-29*t+t*t)*(exponent*(exponent-1)*h
                          +2*exponent*t*sp.diff(h, t)+t*t*sp.diff(h, t, 2))
            +(14-43*t+2*t*t)*(exponent*h+t*sp.diff(h, t))
            +R(2, 9)*t*(t-10)*h)
        require(all(residual.coeff(t, j) == 0 for j in range(order+1)),
                f"Frobenius substitution for exponent {exponent}")
    return {"transformed_ode_coefficients": list(map(str, transformed)),
            "indicial_polynomial": str(indicial),
            "frobenius_even": list(map(str, even)),
            "frobenius_odd": list(map(str, odd))}


def recurrence_kernel(j, degree):
    """Coefficient of u**degree in the recurrence's j-th formal bracket."""
    def shifted(h):
        return sp.rf(R(3, 2)+j, h)/sp.factorial(h) if h >= 0 else ZERO
    middle = {0: 26, 1: 13, 2: 2}.get(degree, 0)
    return sp.expand(27*sp.binomial(R(1, 2)-j, degree)-middle
                     -shifted(degree)+shifted(degree-1)-R(2, 9)*shifted(degree-2))


def scalar_corrections(order):
    """Rational corrections from the original coefficient recurrence."""
    p = [ONE]
    for m in range(1, order+1):
        require(recurrence_kernel(m, 1) == -28*m, "triangular recurrence")
        residual = sum(p[j]*recurrence_kernel(j, m+1-j) for j in range(m))
        p.append(sp.cancel(residual/(28*m)))
    for degree in range(order+2):
        require(sum(p[j]*recurrence_kernel(j, degree-j)
                    for j in range(min(order, degree)+1)) == 0,
                f"formal recurrence coefficient u^{degree}")
    return p


@lru_cache(maxsize=None)
def gamma_ratio_coefficients(a, b, order):
    """Bernoulli-polynomial generator of Gamma(n+a)/Gamma(n+b)."""
    logarithm = [ZERO] + [(-1)**(j+1)*(sp.bernoulli(j+1, a)-sp.bernoulli(j+1, b))
                          / (j*(j+1)) for j in range(1, order+1)]
    result = [ONE]
    for n in range(1, order+1):
        result.append(sp.cancel(sum(j*logarithm[j]*result[n-j]
                                    for j in range(1, n+1))/n))
    return tuple(result)


def transfer_corrections(normalized_odd, order):
    """Transfer normalized Puiseux coefficients into relative n corrections."""
    result = [ZERO]*(order+1)
    for j in range(order+1):
        g = gamma_ratio_coefficients(-j-R(1, 2), ONE, order-j)
        factor = (-1)**j*sp.rf(R(3, 2), j)*normalized_odd[j]
        for h in range(order-j+1):
            result[j+h] += factor*g[h]
    return [sp.expand(value) for value in result]


def family_corrections(even, odd, order):
    """Universal p_{k,m}, polynomial in the fixed weight k and CM value q0.

    binomial(k,2h+1)/k is represented as its polynomial extension. Although
    the generator is symbolic in k, the theorem concerns fixed positive
    integer k, not growing k or a uniform expansion in weight.
    """
    k, q0 = sp.symbols("k q0")
    normalized = []
    for j in range(order+1):
        value = ZERO
        for h in range(j+1):
            choose = sp.prod(k-r for r in range(1, 2*h+1))/sp.factorial(2*h+1)
            left = power(even, k-2*h-1, j-h)
            right = power(odd, 2*h+1, j-h)
            value += choose*q0**h*mul(left, right, j-h)[j-h]
        normalized.append(sp.expand(value))
    p = transfer_corrections(normalized, order)
    # Independent repeated multiplication of E(t)+b*sqrt(t)*O(t), q0=b**2.
    U, V = [ONE]+[ZERO]*order, [ZERO]*(order+1)
    for weight in range(1, 7):
        eu, ov = mul(even, U, order), mul(odd, V, order)
        next_u = [sp.expand(eu[j]+(q0*ov[j-1] if j else 0)) for j in range(order+1)]
        next_v = [sp.expand(a+b) for a, b in zip(mul(odd, U, order), mul(even, V, order))]
        U, V = next_u, next_v
        require(all(sp.expand(normalized[j].subs(k, weight)-V[j]/weight) == 0
                    for j in range(order+1)), f"weight {weight} Puiseux multiplication")
    if order >= 1:
        expected = -R(215, 1008)-R(5, 21)*(k-1)-(k-1)*(k-2)*q0/4
        require(sp.expand(p[1]-expected) == 0, "universal first correction")
    known_k2 = [ONE, -R(65, 144), R(3865, 41472), R(111727, 17915904)]
    require([sp.expand(v.subs(k, 2)) for v in p[:4]] == known_k2[:min(order+1, 4)],
            "displayed k=2 correction coefficients")
    return k, q0, normalized, p


def inverse_coefficients(order):
    """Generate d_j from the formal implicit Lambert-W correction equation.

    lambda*delta-beta*log(1+v*delta)
       +sum ell_j*(v/(1+v*delta))**j = 0.
    The coefficient of the next d_j is lambda. All arithmetic is symbolic.
    """
    lam, beta = sp.symbols("lambda beta", nonzero=True)
    ell = [ZERO] + list(sp.symbols(f"ell1:{order+1}"))
    d = [ZERO]*(order+1)

    def other_terms(values, degree):
        one_plus = [ONE, ZERO] + values[1:degree]
        one_plus = (one_plus + [ZERO]*(degree+1))[:degree+1]
        log = log_series(one_plus, degree)
        residual = [-beta*x for x in log]
        for j in range(1, degree+1):
            inv = power(one_plus, -j, degree-j)
            for h in range(degree-j+1):
                residual[h+j] += ell[j]*inv[h]
        return [sp.expand(x) for x in residual]

    for j in range(1, order+1):
        d[j] = sp.cancel(-other_terms(d, j)[j]/lam)
    residual = other_terms(d, order)
    require(all(sp.expand(lam*d[j]+residual[j]) == 0 for j in range(1, order+1)),
            "formal inverse substitution")
    if order >= 1:
        require(sp.expand(d[1]+ell[1]/lam) == 0, "first inverse coefficient")
    if order >= 2:
        require(sp.expand(d[2]+beta*ell[1]/lam**2+ell[2]/lam) == 0,
                "second inverse coefficient")
    if order >= 3:
        require(sp.expand(d[3]+beta**2*ell[1]/lam**3
                          +(beta*ell[2]+ell[1]**2)/lam**2+ell[3]/lam) == 0,
                "third inverse coefficient")
    return lam, beta, ell, d


def sequence(max_n):
    a = [1, 2]
    for n in range(1, max_n):
        numerator = (26*n*n+13*n+2)*a[-1]+3*(3*n-1)*(3*n-2)*a[-2]
        quotient, remainder = divmod(numerator, (n+1)**2)
        require(remainder == 0, f"integrality at index {n+1}")
        require(quotient > a[-1], f"monotonicity at index {n+1}")
        a.append(quotient)
    return a


def convolution(a, b, max_n):
    return [sum(a[j]*b[n-j] for j in range(n+1)) for n in range(max_n+1)]


def check_norm_coefficients(limit=500):
    """Exact representation counts, with a complete finite search box.

    Q(a,b)>= (a*a+b*b)/2, so |a|,|b|<=sqrt(2*limit) suffices.
    """
    radius = math.isqrt(2*limit)+1
    Q, rectangular = [0]*(limit+1), [0]*(limit+1)
    for a in range(-radius, radius+1):
        for b in range(-radius, radius+1):
            n = a*a+a*b+2*b*b
            if 0 < n <= limit:
                Q[n] += 1
            n = a*a+7*b*b
            if 0 < n <= limit:
                rectangular[n] += 1
    chi = (0, 1, 1, -1, 1, -1, -1)
    for n in range(1, limit+1):
        require(Q[n] == 2*sum(chi[d % 7] for d in range(1, n+1) if n % d == 0),
                f"class-number-one divisor identity at norm {n}")
        expected = Q[n]-(2*Q[n//2] if n % 2 == 0 else 0)+(2*Q[n//4] if n % 4 == 0 else 0)
        require(rectangular[n] == expected, f"index-two Euler factor at norm {n}")
    return limit



def eta(tau):
    cutoff = int(mp.ceil((mp.mp.dps+20)*mp.log(10)/(2*mp.pi*tau.imag)))+5
    nome = mp.exp(2*mp.pi*1j*tau)
    return mp.exp(mp.pi*1j*tau/12)*mp.fprod(1-nome**n for n in range(1, cutoff+1))


def eta_log_derivative(tau):
    cutoff = int(mp.ceil((mp.mp.dps+20)*mp.log(10)/(2*mp.pi*tau.imag)))+5
    nome = mp.exp(2*mp.pi*1j*tau)
    return 2*mp.pi*1j*(mp.mpf(1)/24-mp.fsum(n*nome**n/(1-nome**n)
                                                     for n in range(1, cutoff+1)))


def theta(tau, derivative=False):
    # Generous truncation chosen from the least eigenvalue of Q; this is
    # a high-precision approximation, not a rigorous interval computation.
    least_eigenvalue = (3-mp.sqrt(2))/2
    radius = int(mp.ceil(mp.sqrt((mp.mp.dps+20)*mp.log(10)
                                 /(2*mp.pi*tau.imag*least_eigenvalue))))+2
    terms = []
    for a in range(-radius, radius+1):
        for b in range(-radius, radius+1):
            norm = a*a+a*b+2*b*b
            term = mp.exp(2*mp.pi*1j*tau*norm)
            terms.append(term*(2*mp.pi*1j*norm if derivative else 1))
    return mp.fsum(terms)


def numerical_constants(dps):
    mp.mp.dps = dps
    root7, pi = mp.sqrt(7), mp.pi
    tau0, alpha = 1j/root7, (1+1j*root7)/2
    G = mp.fprod(mp.gamma(mp.mpf(j)/7) for j in (1, 2, 4))
    Gminus = mp.fprod(mp.gamma(mp.mpf(j)/7) for j in (3, 5, 6))
    A0, C = 3*G/(8*pi**2), mp.sqrt(3*pi)/G
    B = -2*mp.sqrt(pi)*C
    eta7, eta0, theta0 = eta(1j*root7), eta(tau0), theta(tau0)
    tau = mp.mpf("0.03")+mp.mpf("0.61")*1j
    th = theta(tau)
    et, et7 = eta(tau), eta(7*tau)
    w = (et7/et)**4
    wp = 4*w*(7*eta_log_derivative(7*tau)-eta_log_derivative(tau))
    X = w/(1+13*w+49*w*w)
    relative = lambda actual, expected: abs(actual/expected-1)
    errors = {
        "eta_gamma_relative": relative(eta7**2, G/(8*7**mp.mpf("0.25")*pi**2)),
        "eta_fricke_relative": relative(eta0, 7**mp.mpf("0.25")*eta7),
        "eta_class_invariant_ratio_relative": relative(abs(eta(alpha))/eta7, mp.sqrt(2)),
        "fundamental_discriminant_minus7_value_relative": relative(7**mp.mpf("0.25")*abs(eta(alpha))**2, G/(4*pi**2)),
        "theta_gamma_relative": relative(theta0, A0),
        "theta_fricke_off_fixed_point_relative": relative(theta(-1/(7*tau)), -1j*root7*tau*th),
        "theta_derivative_relative": relative(theta(tau0, derivative=True), 1j*root7*theta0/2),
        "modular_eta_theta_identity_relative": relative((et*et7/th)**3, X),
        "modular_w_derivative_relative": relative(wp, 2*pi*1j*w*th**2),
        "gauss_gamma_product_relative": relative(G*Gminus, (2*pi)**3/root7),
        "connection_coefficient_relative": relative(B, -3*mp.sqrt(3)/(4*pi*theta0)),
        "fricke_w_value_relative": relative((eta7/eta0)**4, mp.mpf(1)/7),
        "known_weight_two_constant_relative": relative(2*A0*C, 3*mp.sqrt(3)/(4*pi**mp.mpf("1.5"))),
        "q0_gamma_expression_relative": relative((B/A0)**2, 256*pi**6/(3*G**4)),
    }
    chi = (0, 1, 1, -1, 1, -1, -1)
    def L(s):
        return mp.power(7, -s)*mp.fsum(chi[j]*mp.zeta(s, mp.mpf(j)/7) for j in range(1, 7))
    def epstein(s):
        return 2*(1-mp.power(2, 1-s)+mp.power(2, 1-2*s))*mp.zeta(s)*L(s)
    derivative = mp.diff(epstein, 0)
    eta_expression = -2*mp.log(2*pi)-4*mp.log(eta7)
    cutoff = int(mp.ceil((dps+20)*mp.log(10)/(2*pi*root7)))+5
    poisson_expression = (-2*mp.log(2*pi)+pi*root7/3
                          +4*mp.fsum(mp.exp(-2*pi*root7*n*j)/j
                                    for n in range(1, cutoff+1)
                                    for j in range(1, cutoff+1)))
    errors.update({
        "L_at_zero_absolute": abs(L(0)-1),
        "L_derivative_absolute": abs(mp.diff(L, 0)+mp.log(7)-mp.log(G/Gminus)),
        "epstein_at_zero_absolute": abs(epstein(0)+1),
        "epstein_derivative_eta_absolute": abs(derivative-eta_expression),
        "epstein_derivative_gamma_absolute": abs(derivative-mp.log(14/pi)+mp.log(G/Gminus)),
        "epstein_derivative_poisson_absolute": abs(derivative-poisson_expression),
        "normalized_epstein_derivative_absolute": abs(mp.diff(lambda s: root7**s*epstein(s), 0)
                                                        -eta_expression+mp.log(root7)),
    })
    tolerance = mp.power(10, -(dps-20))
    require(max(errors.values()) < tolerance, "CM/modular/Epstein numerical tolerance")
    summary = {
        "working_decimal_digits": dps,
        "comparison_tolerance": mp.nstr(tolerance, 8),
        "errors": {key: mp.nstr(value, 12) for key, value in errors.items()},
        "G": mp.nstr(G, dps-10), "A0": mp.nstr(A0, dps-10),
        "C": mp.nstr(C, dps-10), "B": mp.nstr(B, dps-10),
        "q0": mp.nstr((B/A0)**2, dps-10),
        "epstein_derivative_at_zero": mp.nstr(derivative, dps-10),
        "normalization": "E_y(s)=sum' (m^2+y^2*n^2)^(-s); E_y'(0)=-2 log(2 pi)-4 log eta(i y). For H_y=y^s E_y, H_y'(0)=E_y'(0)-log y.",
        "certification": "Floating-point checks with truncated products/sums; no interval certification.",
    }
    return A0, C, (B/A0)**2, summary


def indices(max_n):
    return sorted({n for n in (25, 50, 100, 200, 400, 800, 1600, max_n) if 10 <= n <= max_n})


def residual_rows(a, constant, corrections, max_n, order):
    rows = []
    for n in indices(max_n):
        ratio = mp.mpf(a[n])/(constant*mp.power(27, n)*mp.power(n, -mp.mpf("1.5")))
        residuals = []
        for truncation in range(order+1):
            approx = mp.fsum(corrections[j]/mp.power(n, j) for j in range(truncation+1))
            residuals.append(mp.nstr((ratio-approx)*mp.power(n, truncation+1), 22))
        rows.append({"n": n, "normalized_ratio": mp.nstr(ratio, 25),
                     "scaled_residuals_M_0_through_order": residuals})
    return rows


def numerical_inverse(a, constant, p, inverse_data, max_n, order):
    lam_symbol, beta_symbol, ell_symbols, d = inverse_data
    lam, beta = mp.log(27), mp.mpf("1.5")
    # Log coefficients are obtained by the same finite algebraic recurrence,
    # evaluated here at high precision; no fitted inverse coefficients occur.
    ell_values = [mp.mpf(0)]
    for n in range(1, order+1):
        ell_values.append(p[n]-mp.fsum(j*ell_values[j]*p[n-j] for j in range(1, n))/n)
    args = (lam_symbol, beta_symbol, *ell_symbols[1:])
    numeric_d = [mp.mpf(0)] + [sp.lambdify(args, expr, "mpmath")
                              (lam, beta, *ell_values[1:]) for expr in d[1:]]
    rows = []
    for n in indices(max_n):
        Y = mp.mpf(a[n])
        base = -beta/lam*mp.lambertw(-lam/beta*(constant/Y)**(1/beta), -1)
        base = mp.re(base)
        estimate = base+mp.fsum(numeric_d[j]/base**j for j in range(1, order+1))
        def log_forward(nu):
            polynomial = mp.fsum(p[j]/nu**j for j in range(order+1))
            return mp.log(constant)+lam*nu-beta*mp.log(nu)+mp.log(polynomial)-mp.log(Y)
        root = mp.findroot(log_forward, (base, base+mp.mpf("0.1")))
        require(abs(log_forward(root)) < mp.power(10, -(mp.mp.dps-15)),
                "numerical forward-truncation root")
        rows.append({"n": n, "Y": "exact sequence coefficient at index n",
                     "base_inverse_minus_n": mp.nstr(base-n, 22),
                     "corrected_inverse_minus_n": mp.nstr(estimate-n, 22),
                     "corrected_error_scaled_by_n_to_order_plus_1": mp.nstr((estimate-n)*mp.power(n, order+1), 22),
                     "forward_truncation_root_minus_n": mp.nstr(root-n, 22),
                     "formal_inverse_minus_forward_root_scaled": mp.nstr((estimate-root)*base**(order+1), 22)})
    return {"inverse_coefficients_numeric": [mp.nstr(v, 30) for v in numeric_d[1:]],
            "rows": rows,
            "rounding_warning": "These samples lie exactly at discrete thresholds. No exact-ceiling rule, effective K, cutoff, or certified enclosure is inferred from residuals."}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, default=Path("replay_results.json"), help="JSON output path (default: ./replay_results.json)")
    parser.add_argument("--order", type=int, default=6, help="fixed expansion order, including corrections 1 through M (default: 6)")
    parser.add_argument("--max-n", type=int, default=1600, help="largest scalar recurrence index (default: 1600)")
    parser.add_argument("--dps", type=int, default=100, help="mpmath working decimal digits (default: 100)")
    args = parser.parse_args()
    if args.order < 0 or args.max_n < 25 or args.dps < 50:
        parser.error("require --order >= 0, --max-n >= 25, and --dps >= 50")
    # Keep enough guard digits for the displayed n**(M+1)-scaled residuals.
    minimum_dps = max(50, 30+(args.order+1)*len(str(args.max_n)))
    if args.dps < minimum_dps:
        parser.error(f"use --dps >= {minimum_dps} for these order/index settings")
    start = time.perf_counter()
    print("Computing exact Frobenius, recurrence, transfer, family, and inverse coefficients...", flush=True)
    M = args.order
    e, o = frobenius(0, M), frobenius(R(1, 2), M)
    ode = check_ode_and_frobenius(e, o, M)
    scalar = scalar_corrections(M)
    require(scalar == transfer_corrections(o, M), "scalar recurrence/transfer equality")
    expected = [ONE, -R(215, 1008), -R(1265, 290304), R(4683055, 877879296)]
    require(scalar[:4] == expected[:min(M+1, 4)], "displayed scalar corrections")
    k, q0_symbol, family_odd, family_p = family_corrections(e, o, M)
    require([sp.expand(p.subs(k, 1)) for p in family_p] == scalar, "family specialization k=1")
    inverse_data = inverse_coefficients(M)
    norm_count = check_norm_coefficients()
    print("Checking CM, eta/theta, Fricke, and Epstein normalizations...", flush=True)
    A0, C, q0, constants = numerical_constants(args.dps)
    a = sequence(args.max_n)
    checked_convolutions = min(args.max_n, 40)
    for n in range(checked_convolutions+1):
        actual = sum(a[j]*a[n-j] for j in range(n+1))
        expected = sum(math.comb(n, j)**2*math.comb(2*j, n)*math.comb(n+j, j)
                       for j in range(n+1) if 2*j >= n)
        require(actual == expected, f"A183204 binomial/convolution identity at n={n}")
    print("Computing empirical coefficient and Lambert-W inverse residuals...", flush=True)
    families = []
    family_max_n = min(args.max_n, 400)
    family_values = a[:family_max_n+1]
    for weight in (1, 2, 3):
        if weight > 1:
            family_values = convolution(family_values, a, family_max_n)
        values = a if weight == 1 else family_values
        max_n = args.max_n if weight == 1 else family_max_n
        coefficient_functions = [sp.lambdify(q0_symbol, p.subs(k, weight), "mpmath") for p in family_p]
        coefficients = [mp.mpf(f(q0)) for f in coefficient_functions]
        Ck = weight*A0**(weight-1)*C
        families.append({"k": weight, "max_n": max_n,
                         "leading_constant": mp.nstr(Ck, 50),
                         "corrections": [mp.nstr(c, 40) for c in coefficients],
                         "coefficient_residuals": residual_rows(values, Ck, coefficients, max_n, M),
                         "inverse_checks": numerical_inverse(values, Ck, coefficients, inverse_data, max_n, M)})
    lam, beta, ell, inverse = inverse_data
    result = {
        "status": "PASS",
        "scope": "Finite exact algebraic checks plus non-certified high-precision numerical corroboration. Analytic proofs and fixed-order remainder arguments are in the accompanying article.",
        "versions": {"python": platform.python_version(), "sympy": sp.__version__, "mpmath": mp.__version__},
        "parameters": {"order": M, "max_n": args.max_n, "family_max_n": family_max_n, "dps": args.dps},
        "exact_checks": {**ode, "scalar_recurrence_transfer_coefficients": list(map(str, scalar)),
                         "recurrence_integrality_and_monotonicity_through_n": args.max_n,
                         "initial_coefficients": a[:12],
                         "norm_and_suborder_coefficients_through": norm_count,
                         "k2_convolution_binomial_identity_through_n": checked_convolutions,
                         "family_weights_checked_by_direct_multiplication": list(range(1, 7)),
                         "family_normalized_odd_coefficients": list(map(str, family_odd)),
                         "family_relative_corrections": list(map(str, family_p)),
                         "family_parameter": "q0=(B/A0)^2=256*pi^6/(3*G^4); k is fixed positive integer",
                         "scalar_logarithmic_coefficients": list(map(str, log_series(scalar, M)[1:])),
                         "universal_inverse_coefficients": list(map(str, inverse[1:])),
                         "inverse_parameters": "lambda=log(27), beta=3/2, ell_j=[u^j]log(sum p_{k,m}u^m)",
                         "inverse_equation": "lambda*delta-beta*log(1+v*delta)+sum ell_j*(v/(1+v*delta))^j=0"},
        "high_precision_identity_checks": constants,
        "empirical_family_residuals": families,
        "residual_convention": "For each M=0,...,order, report n^(M+1)*(a_{k,n}/(C_k*27^n*n^(-3/2))-sum_{j=0}^M p_{k,j}/n^j). For M<order the expected limit is the next computed correction p_{k,M+1}; residuals do not bound remainders.",
        "prior_work": [
            {"author": "Jesus Guillera and Wadim Zudilin", "title": "Ramanujan-type formulae for 1/pi: The art of translation", "publication": "The Legacy of Srinivasa Ramanujan, Ramanujan Mathematical Society Lecture Notes Series 20 (2013), 181-195", "url": "https://arxiv.org/abs/1302.0548v2", "role": "Prior modular radial-connection mechanism; Example 5 and equations (23), (27)."},
            {"author": "Lynette Anne O'Brien", "title": "Modular forms and two new integer sequences at level 7", "year": 2016, "url": "https://hdl.handle.net/10179/11137", "role": "Recurrence and modular identities; scalar asymptotic conjecture."},
            {"author": "Michael D. Hirschhorn", "title": "A sequence considered by Shaun Cooper", "publication": "New Zealand Journal of Mathematics 43 (2013), 37-42", "url": "https://web.maths.unsw.edu.au/~mikeh/webpapers/paper182.pdf", "role": "Previously established k=2 asymptotic result through sixth order, not a new case here."},
            {"author": "Shaun Cooper", "title": "Apéry-like sequences defined by four-term recurrence relations", "publication": "Contemporary Mathematics 818 (2025), 137-179", "url": "https://doi.org/10.1090/conm/818/16373", "role": "Section 10 discusses the known level-7 weight-two asymptotics."},
            {"title": "OEIS A279619", "url": "https://oeis.org/A279619"},
            {"title": "OEIS A183204", "url": "https://oeis.org/A183204", "role": "Known k=2 sequence and binomial sum."},
            {"author": "Don Zagier", "title": "Elliptic Modular Forms and Their Applications", "url": "https://www.its.caltech.edu/~matilde/Zagier123ModularForms.pdf", "role": "Classical discriminant -7 CM period, printed p. 95."},
        ],
        "duration_seconds": round(time.perf_counter()-start, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(f"PASS: all requested finite checks completed in {result['duration_seconds']:.3f} seconds.")
    print(f"Results: {args.output}")
    print("Numerical residuals are empirical; no interval or integer-rounding certification is claimed.")


if __name__ == "__main__":
    main()
