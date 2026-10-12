#!/usr/bin/env python3
"""Finite symbolic audits and high-precision diagnostics for local polylog jets.

The symbolic identities are exact in SymPy. Numerical evaluations use mpmath
and are diagnostics, not directed-rounding certificates or substitutes for the
all-order arguments in the article. No network access or repository mutation.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import time

import mpmath as mp
import sympy as sp


def mul(a, b, n):
    """Truncated ordinary-series product with expanded exact coefficients."""
    out = [sp.S.Zero] * (n + 1)
    for i in range(min(n, len(a) - 1) + 1):
        if a[i] == 0:
            continue
        for j in range(min(n - i, len(b) - 1) + 1):
            if b[j] != 0:
                out[i + j] += a[i] * b[j]
    return [sp.expand(v) for v in out]


def power(a, k, n):
    out = [sp.S.One] + [sp.S.Zero] * n
    for _ in range(k):
        out = mul(out, a, n)
    return out


def exp_coefficients(log_coeff, n):
    out = [sp.S.One] + [sp.S.Zero] * n
    for j in range(1, n + 1):
        out[j] = sp.expand(sum(r * log_coeff[r] * out[j-r]
                              for r in range(1, j + 1)) / j)
    return out


def symbolic_conjugation(max_q=5):
    """Build raw pole-paired jets, then independently convolve reciprocal jets."""
    L, gamma = sp.symbols("L gamma")
    zeta = {r: sp.Symbol(f"zeta_{r}") for r in range(2, max_q + 1)}
    stieltjes = sp.symbols(f"g0:{max_q}")
    checks = []
    for p in (1, 2, 3):
        log_a = [sp.S.Zero, gamma - sp.harmonic(p)]
        for r in range(2, max_q + 1):
            log_a.append((zeta[r] + (-1)**r * sp.harmonic(p, r)) / r)
        a = exp_coefficients(log_a, max_q)
        d = exp_coefficients([-x for x in log_a], max_q)
        ae = mul(a, [(-L)**j / sp.factorial(j)
                     for j in range(max_q + 1)], max_q)
        # Raw R_j are Taylor coefficients, not derivatives. Analytic t-tail
        # is set to zero here to test the singular logarithmic polynomial.
        raw = [(-1)**j * stieltjes[j] / sp.factorial(j) - ae[j+1]
               for j in range(max_q)]
        eps_zeta = [sp.S.One] + [(-1)**j * stieltjes[j] / sp.factorial(j)
                                   for j in range(max_q)]
        eps_raw = [sp.S.Zero] + raw
        combined = mul(d, [eps_raw[j] - eps_zeta[j]
                           for j in range(max_q + 1)], max_q)
        for q in range(1, max_q + 1):
            normalized = sp.expand((-1)**(q+1) * sp.factorial(q) * combined[q])
            assert normalized == L**q
            checks.append({"p": p, "q": q, "identity": "normalized singular jet = L^q"})
    return {"status": "passed", "exact_checks": len(checks), "checks": checks,
            "constants": "Euler gamma, zeta values, and Stieltjes constants treated as independent symbols"}


def symbolic_inverse(max_n=5):
    eta, D = sp.symbols("eta D")
    r = sp.symbols(f"r0:{max_n}")
    records = []
    total_residual_checks = 0
    total_pole_checks = 0
    total_explicit_checks = 0
    for p in (1, 2, 3):
        for q in (1, 2, 3, 4):
            # h(z) coefficients are formed directly from H(1+z), using
            # finite ordinary-series multiplication. D denotes h(0);
            # keep it independent until the pole is evaluated.
            log_one_plus = [sp.S.Zero] + [sp.Rational((-1)**(j+1), j)
                                          for j in range(1, max_n + 1)]
            u = [sp.S.One] + [-eta * log_one_plus[j]
                             for j in range(1, max_n + 1)]
            H = mul([sp.binomial(p, j) for j in range(max_n + 1)],
                    power(u, q, max_n), max_n)
            assert sp.expand(H[1] - (p - q*eta)) == 0
            h = [D] + H[2:]
            h_rest_over_D = [sp.S.Zero] + [h[j] / D for j in range(1, max_n)]

            r_powers = {k: power(list(r), k, max_n-k)
                        for k in range(1, max_n + 1)}
            v_formula = [sp.S.Zero] * (max_n + 1)
            for n in range(1, max_n + 1):
                vn = sp.S.Zero
                for k in range(1, n + 1):
                    # Negative binomial series for h(z)^(-k).
                    h_inverse_power = [sp.S.Zero] * k
                    for j in range(k):
                        rest_power = power(h_rest_over_D, j, k-1)
                        factor = sp.binomial(-k, j) / D**k
                        h_inverse_power = [sp.expand(a + factor*b)
                                           for a, b in zip(h_inverse_power, rest_power)]
                    z_factor = mul([sp.binomial(k*p+n, j) for j in range(k)],
                                   h_inverse_power, k-1)[k-1]
                    vn += (-eta**q)**k * r_powers[k][n-k] * z_factor / k
                v_formula[n] = sp.expand(vn)

            # Independently substitute into the implicit equation. Build
            # each v_n by cancelling the coefficient with known lower v_j.
            v_recurrence = [sp.S.Zero] * (max_n + 1)
            for n in range(1, max_n + 1):
                W = v_recurrence[:n] + [sp.S.Zero]
                known = sp.S.Zero
                for j in range(2, n + 1):
                    known += H[j] * power(W, j, n)[n]
                one_plus_W = W[:]
                one_plus_W[0] = sp.S.One
                for j in range(n):
                    known += eta**q * r[j] * power(one_plus_W, p+1+j, n-j-1)[n-j-1]
                v_recurrence[n] = sp.expand(-known / D)
                assert sp.expand(v_recurrence[n] - v_formula[n]) == 0
                total_residual_checks += 1

                # Multiply out the largest permitted denominator and test
                # actual nonzero leading coefficient at eta=p/q.
                scaled = sp.expand(D**(2*n-1) * v_formula[n])
                assert not scaled.has(sp.zoo)
                leading = scaled.subs(D, 0)
                assert not leading.has(sp.zoo, sp.nan)
                eta0 = sp.Rational(p, q)
                actual = sp.expand(leading.subs(eta, eta0))
                expected = -sp.catalan(n-1) * (eta0**q*r[0])**n * (-sp.Rational(p*p, 2*q))**(n-1)
                assert sp.expand(actual - expected) == 0
                total_pole_checks += 1

            explicit_v1 = -eta**q*r[0]/D
            explicit_v2 = -eta**q*r[1]/D + eta**(2*q)*r[0]**2*((p+1)*D-H[2])/D**3
            assert sp.expand(v_formula[1] - explicit_v1) == 0
            assert sp.expand(v_formula[2] - explicit_v2) == 0
            assert sp.expand(2*H[2] - ((p-q*eta)**2-(p-q*eta)-q*eta**2)) == 0
            total_explicit_checks += 3
            records.append({"p": p, "q": q, "coefficient_orders": list(range(1, max_n+1)),
                            "symbolic_tail_coefficients": [str(x) for x in r]})
    return {"status": "passed", "recurrence_formula_checks": total_residual_checks,
            "sharp_pole_checks": total_pole_checks, "explicit_coefficient_checks": total_explicit_checks,
            "checks": records,
            "note": "D is an independent slope during coefficient comparisons; at the pole eta=p/q and D=0."}


def gamma_inverse_unit(eps, p):
    return mp.fprod(1 + eps/j for j in range(1, p+1)) / mp.gamma(1-eps)


def hurwitz(s, a):
    if a == mp.mpf('0.5'):
        return (mp.power(2, s)-1) * mp.zeta(s)
    return mp.zeta(s, a)


def unit_coeffs(p, q):
    return [mp.diff(lambda eps: gamma_inverse_unit(eps, p), 0, j)/mp.factorial(j)
            for j in range(q+1)]


def defining_series_jets(p, q, a, t):
    """Independent log-weighted defining sums, with a monotone tail bound.

    No finite differences of mpmath.polylog are used: its integer-order
    algorithm changes can compromise order-derivative checks.
    """
    sigma = mp.re(t)
    assert sigma > 0
    n_terms = int(mp.ceil((mp.mp.dps + 10) * mp.log(10) / sigma))
    ratio = mp.exp(-t)
    exponential = mp.exp(-a*t)
    terms = [[] for _ in range(q)]
    for n in range(n_terms):
        x = n+a
        base = exponential / x**(p+1)
        log_weight = -mp.log(x)
        multiplier = mp.mpf(1)
        for j in range(q):
            terms[j].append(base*multiplier)
            multiplier *= log_weight
        exponential *= ratio
    sums = [mp.fsum(row) for row in terms]
    x = n_terms+a
    # log(x)^j / x^(p+1) decreases for log(x)>j/(p+1).
    assert mp.log(x) > mp.mpf(q-1)/(p+1)
    bounds = [mp.exp(-sigma*x)*mp.log(x)**j/x**(p+1)/(1-mp.exp(-sigma))
              for j in range(q)]
    return sums, n_terms, bounds


def actual_normalized_jet(p, q, a, t, d=None, with_provenance=False):
    """From defining-series order jets and Hurwitz, not a local t expansion."""
    d = unit_coeffs(p, q) if d is None else d
    f_jets, n_terms, bounds = defining_series_jets(p, q, a, t)
    raw_jet = []
    for order in range(q):
        head = mp.fsum(mp.diff(lambda e: hurwitz(p+1+e-j, a), 0, order)
                       * (-t)**j/mp.factorial(j) for j in range(p))
        raw_jet.append(mp.factorial(p)/(-t)**p * (f_jets[order]-head)
                       / mp.factorial(order))
    eps_raw_minus_zeta = [-mp.mpf(1)]
    for j in range(1, q+1):
        eps_raw_minus_zeta.append(raw_jet[j-1] - (-1)**(j-1)*mp.stieltjes(j-1, a)/mp.factorial(j-1))
    c = mp.fsum(d[j]*eps_raw_minus_zeta[q-j] for j in range(q+1))
    value = t**p * (-1)**(q+1) * mp.factorial(q) * c
    if with_provenance:
        return value, {"defining_sum_terms": n_terms,
                       "absolute_tail_bounds_for_derivative_orders": [num(x) for x in bounds],
                       "method": "explicit exponentially convergent sums of log-weighted terms; no polylog finite differences"}
    return value


def analytic_tail_coeffs(p, q, a, n_terms, d=None):
    """Return coefficients a_l of analytic tail sum_(l>=1) a_l t^l."""
    d = unit_coeffs(p, q) if d is None else d
    out = []
    for ell in range(1, n_terms+1):
        z = [mp.diff(lambda e: hurwitz(1+e-ell, a), 0, j)/mp.factorial(j)
             for j in range(q)]
        coeff = mp.fsum(d[j]*z[q-1-j] for j in range(q))
        out.append((-1)**(q+1+ell)*mp.factorial(q)*mp.factorial(p)/mp.factorial(p+ell)*coeff)
    return out


def normal_form_value(p, q, t, coeffs):
    L = -mp.log(t)
    return t**p * (L**q + mp.fsum(a*t**ell for ell, a in enumerate(coeffs, 1)))


def num(v, digits=45):
    if isinstance(v, mp.mpc):
        return {"real": mp.nstr(v.real, digits), "imag": mp.nstr(v.imag, digits)}
    return mp.nstr(v, digits)


def numerical_checks(dps=85):
    mp.mp.dps = dps
    configs = [(1, 2, mp.mpf(1), mp.mpc('0.012', '0.004')),
               (2, 3, mp.mpf('0.5'), mp.mpc('0.008', '-0.003')),
               (3, 1, mp.mpf(1), mp.mpc('0.011', '0.002')),
               (1, 3, mp.mpf('0.5'), mp.mpc('0.007', '0.005'))]
    jets = []
    for p, q, a, t in configs:
        d = unit_coeffs(p, q)
        coeffs = analytic_tail_coeffs(p, q, a, 14, d)
        actual, provenance = actual_normalized_jet(p, q, a, t, d, True)
        expected = normal_form_value(p, q, t, coeffs)
        error = abs(actual-expected)
        assert error < mp.mpf('1e-30')
        first_formula = (-1)**q * mp.mpf(q)/(p+1) * mp.diff(
            lambda e: gamma_inverse_unit(e, p)*hurwitz(e, a), 0, q-1)
        first_error = abs(coeffs[0]-first_formula)
        assert first_error < mp.mpf('1e-70')
        jets.append({"p": p, "q": q, "a": num(a), "t": num(t),
                     "actual_order_jet": num(actual), "normal_form": num(expected),
                     "absolute_error": num(error), "analytic_tail_terms": 14,
                     "first_tail_coefficient_error": num(first_error),
                     "reference_provenance": provenance})

    inverses = []
    for p, q, a, T in [(1, 2, mp.mpf(1), mp.mpf('0.01')),
                       (2, 3, mp.mpf('0.5'), mp.mpf('0.01'))]:
        d = unit_coeffs(p, q)
        coeffs = analytic_tail_coeffs(p, q, a, 24, d)
        ell = -mp.log(T)
        eta = 1/ell
        y = T**p*ell**q
        recovered_ell = -mp.mpf(q)/p*mp.lambertw(-mp.mpf(p)/q*y**(mp.mpf(1)/q), -1)
        assert abs(recovered_ell-ell) < mp.mpf('1e-75')
        r0, r1 = coeffs[:2]
        D = p-q*eta
        H2 = D**2-D-q*eta**2
        v1 = -eta**q*r0/D
        v2 = -eta**q*r1/D + eta**(2*q)*r0**2*((p+1)*D-H2/2)/D**3
        approximation_1 = T*(1+v1*T)
        approximation_2 = T*(1+v1*T+v2*T**2)
        root = mp.findroot(lambda t: normal_form_value(p, q, t, coeffs)-y,
                           (T, approximation_2), tol=mp.mpf('1e-78'))
        original_value, provenance = actual_normalized_jet(p, q, a, root, d, True)
        original_residual = abs(original_value-y)
        error0 = abs(T-root)
        error1 = abs(approximation_1-root)
        error2 = abs(approximation_2-root)
        assert error2 < error1 < error0
        assert original_residual < mp.mpf('1e-60')
        inverses.append({"p": p, "q": q, "a": num(a), "T": num(T),
                         "y": num(y), "eta": num(eta), "root": num(root),
                         "core_error": num(error0), "first_correction_error": num(error1),
                         "second_correction_error": num(error2),
                         "actual_order_jet_residual_at_root": num(original_residual),
                         "root_method": "findroot of 24-term convergent analytic normal form; checked against log-weighted defining sums",
                         "reference_provenance": provenance})
    return {"status": "passed", "precision_decimal_digits": dps,
            "arithmetic": "mpmath high precision, without directed rounding",
            "jet_diagnostics": jets, "inverse_diagnostics": inverses}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('verification_local_jets.json'))
    parser.add_argument('--skip-numeric', action='store_true')
    args = parser.parse_args()
    start = time.perf_counter()
    result = {"purpose": "finite symbolic audit and independent numerical diagnostics",
              "proof_status": "The all-order results are proved in the article; this script checks finite instances.",
              "environment": {"python": platform.python_version(), "sympy": sp.__version__,
                              "mpmath": mp.__version__},
              "source_snapshot": "9ec0f0406afe7a5475b03ff65ed91f7e283979b8"}
    result['gamma_conjugation'] = symbolic_conjugation()
    result['inverse_coefficients'] = symbolic_inverse()
    if not args.skip_numeric:
        result['numerical'] = numerical_checks()
    result['status'] = 'passed'
    result['elapsed_seconds'] = round(time.perf_counter()-start, 3)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({"status": result['status'], "output": str(args.output.resolve()),
                      "elapsed_seconds": result['elapsed_seconds'],
                      "exact_conjugation_checks": result['gamma_conjugation']['exact_checks'],
                      "exact_recurrence_checks": result['inverse_coefficients']['recurrence_formula_checks'],
                      "exact_pole_checks": result['inverse_coefficients']['sharp_pole_checks'],
                      "numerical_enabled": not args.skip_numeric}, indent=2))


if __name__ == '__main__':
    main()
