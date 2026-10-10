#!/usr/bin/env python3
"""Independent coefficient-sum checks for the Gauss--Stieltjes jet theorem.

The left side is evaluated by direct summation and a Bernoulli-polynomial
gamma-ratio tail.  It does not use Gauss summation or the proposed closed form.
The tail is an asymptotic acceleration; agreement under a second truncation is
a numerical diagnostic, not a rigorous interval certificate or a proof.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def indices(caps):
    return sorted(itertools.product(*(range(k + 1) for k in caps)), key=sum)


def poly_mul(a, b, caps):
    out = {}
    for i, ai in a.items():
        for j, bj in b.items():
            k = tuple(x + y for x, y in zip(i, j))
            if all(x <= c for x, c in zip(k, caps)):
                out[k] = out.get(k, mp.mpf(0)) + ai * bj
    return out


def poly_exp(a, caps):
    zero = (0,) * len(caps)
    out = {zero: mp.mpf(1)}
    power = {zero: mp.mpf(1)}
    for k in range(1, sum(caps) + 1):
        power = poly_mul(power, a, caps)
        for i, v in power.items():
            out[i] = out.get(i, mp.mpf(0)) + v / mp.factorial(k)
    return out


def term_log_jet(n, a, b, caps):
    """log(w_n(a+u,b+v,s)/w_n(a,b,0))."""
    out = {}
    for p, q, r in indices(caps):
        degree = p + q + r
        if not degree:
            continue
        value = -mp.polygamma(degree - 1, n + a + b)
        if q == r == 0:
            value += mp.polygamma(degree - 1, n + a)
        if p == r == 0:
            value += mp.polygamma(degree - 1, n + b)
        out[p, q, r] = value / (
            mp.factorial(p) * mp.factorial(q) * mp.factorial(r)
        )
    return out


def ratio_log_jet(a, b, caps):
    """log R(u,v,s), where R(u,v,0)=1 identically."""
    out = {}
    for p, q, r in indices(caps):
        if r == 0:
            continue
        value = mp.mpf(0)
        if p == q == 0:
            value += mp.polygamma(r - 1, 1) / mp.factorial(r)
        if q == 0:
            value -= mp.polygamma(p + r - 1, a) / (
                mp.factorial(p) * mp.factorial(r)
            )
        if p == 0:
            value -= mp.polygamma(q + r - 1, b) / (
                mp.factorial(q) * mp.factorial(r)
            )
        out[p, q, r] = value
    return out


def bernoulli_log_tail(a, b, c, k, caps):
    """Jet of x^-k coefficient in log(w_n x^(1+s)), x=n+c."""
    d = {}
    degree_max = k + 1
    prefactor = mp.mpf((-1) ** (k + 1)) / (k * (k + 1))
    for p, q, r in indices(caps):
        total = p + q + r
        if total > degree_max:
            continue
        fac = mp.factorial(degree_max) / (
            mp.factorial(degree_max - total)
            * mp.factorial(p) * mp.factorial(q) * mp.factorial(r)
        )
        v = -fac * mp.bernpoly(degree_max - total, a + b - c)
        if q == r == 0:
            v += mp.binomial(degree_max, p) * mp.bernpoly(degree_max - p, a - c)
        if p == r == 0:
            v += mp.binomial(degree_max, q) * mp.bernpoly(degree_max - q, b - c)
        if total == 0:
            v -= mp.bernpoly(degree_max, 1 - c)
        d[p, q, r] = prefactor * v
    return d


def numerical_series_jet(a, b, c, nterms, ntail, caps=(1, 1, 2)):
    """All ordinary Taylor coefficients through the specified box."""
    keys = indices(caps)
    result = {key: mp.mpf(0) for key in keys}
    weight = mp.gamma(a) * mp.gamma(b) / mp.gamma(a + b)
    for n in range(nterms):
        expjet = poly_exp(term_log_jet(n, a, b, caps), caps)
        x = n + c
        for p, q, r in keys:
            value = weight * expjet.get((p, q, r), 0)
            if p == q == 0:
                value -= (-mp.log(x)) ** r / (mp.factorial(r) * x)
            result[p, q, r] += value
        weight *= (n + a) * (n + b) / ((n + a + b) * (n + 1))

    d = {j: bernoulli_log_tail(a, b, c, j, caps) for j in range(1, ntail + 1)}
    e = {0: {(0, 0, 0): mp.mpf(1)}}
    for k in range(1, ntail + 1):
        ek = {}
        for j in range(1, k + 1):
            product = poly_mul(d[j], e[k - j], caps)
            for key, value in product.items():
                ek[key] = ek.get(key, mp.mpf(0)) + mp.mpf(j) * value / k
        e[k] = ek
        zeta_jet = [
            mp.zeta(k + 1, nterms + c, derivative=r) / mp.factorial(r)
            for r in range(caps[2] + 1)
        ]
        for p, q, r in keys:
            result[p, q, r] += sum(
                ek.get((p, q, j), 0) * zeta_jet[r - j] for j in range(r + 1)
            )
    return result


def closed_form_jet(a, b, c, caps=(1, 1, 2)):
    extended = caps[0], caps[1], caps[2] + 1
    r = poly_exp(ratio_log_jet(a, b, extended), extended)
    out = {}
    for p, q, k in indices(caps):
        value = r.get((p, q, k + 1), 0)
        if p == q == 0:
            value -= (-1) ** k * mp.stieltjes(k, c) / mp.factorial(k)
        out[p, q, k] = value
    return out


def show(x):
    if isinstance(x, (mp.ctx_mp_python.mpc, complex)):
        return {"real": mp.nstr(mp.re(x), 55), "imag": mp.nstr(mp.im(x), 55)}
    return mp.nstr(x, 55)


def symbolic_choi_checks():
    h = sp.symbols("H1:7")
    e = [sp.Integer(1)]
    for n in range(1, 7):
        e.append(sp.expand(sum(
            sp.binomial(n - 1, j - 1) * e[n - j]
            * (-1) ** (j - 1) * sp.factorial(j - 1) * h[j - 1]
            for j in range(1, n + 1)
        )))
    z = sp.symbols("z")
    # The corrected H_n E_r generating function is
    # (1 + sum_{j>=1} zeta(j+1) z^j)/(1-z).
    sigma = sp.symbols("Z2:8")
    numerator = 1 + sum(sigma[j - 1] * z ** j for j in range(1, 7))
    rhs = sp.series(numerator / (1 - z), z, 0, 7).removeO()
    coefficient_checks = []
    for r in range(7):
        expected = 1 + sum(sigma[:r])
        assert sp.expand(rhs.coeff(z, r) - expected) == 0
        coefficient_checks.append({
            "r": r,
            "corrected_value": str(sp.factorial(r) * expected),
        })
    sixth_printed_difference = -120 * (h[4] - h[5])
    return {
        "bell_polynomials": {str(r): str(e[r]) for r in range(1, 7)},
        "all_order_coefficient_checks": coefficient_checks,
        "equation_40_second_numerator_printed_minus_corrected": str(sixth_printed_difference),
        "equation_46_bad_term_printed_minus_corrected": str(45*h[0]**5-45*h[0]**3*h[1]**2),
        "corollary_5_and_conjecture_6_rhs_correction": "Divide displayed RHSs (41)-(46) by 2, after correcting numerator typos.",
    }


def scalar_asymptotic_coefficients(a, b, c, s, order):
    d = [mp.mpf(0)]
    for j in range(1, order + 1):
        d.append(mp.mpf((-1) ** (j + 1)) / (j * (j + 1)) * (
            mp.bernpoly(j + 1, a - c) + mp.bernpoly(j + 1, b - c)
            - mp.bernpoly(j + 1, a + b + s - c) - mp.bernpoly(j + 1, 1 - c)
        ))
    coef = [mp.mpf(1)]
    for k in range(1, order + 1):
        coef.append(sum(j * d[j] * coef[k - j] for j in range(1, k + 1)) / k)
    return coef


def central_negative_balance(nterms, ntail):
    """Direct bracket at s=-1, including the n=0 reciprocal-gamma zero."""
    d = mp.mpf(1)
    total = mp.mpf(0)
    for n in range(nterms):
        total += mp.pi * n * d - 1 + mp.mpf(1) / (4 * (n + 1))
        d *= ((mp.mpf(n) + mp.mpf("0.5")) / (n + 1)) ** 2
    coef = scalar_asymptotic_coefficients(mp.mpf("0.5"), mp.mpf("0.5"), 1, -1, ntail)
    return total + sum(coef[j] * mp.zeta(j, nterms + 1) for j in range(2, ntail + 1))


def symbolic_residue_checks():
    a, b, c = sp.symbols("a b c")
    result = []
    for r in range(5):
        d = [sp.Integer(0)]
        for j in range(1, r + 1):
            d.append(sp.expand(sp.Rational((-1) ** (j + 1), j * (j + 1)) * (
                sp.bernoulli(j + 1, a - c) + sp.bernoulli(j + 1, b - c)
                - sp.bernoulli(j + 1, a + b - r - c) - sp.bernoulli(j + 1, 1 - c)
            )))
        coef = [sp.Integer(1)]
        for k in range(1, r + 1):
            coef.append(sp.expand(sum(j*d[j]*coef[k-j] for j in range(1, k+1)) / k))
        expected = (-1)**r * sp.rf(1-a, r) * sp.rf(1-b, r) / sp.factorial(r)
        difference = sp.expand(coef[r] - expected)
        assert difference == 0, (r, difference)
        assert sp.diff(coef[r], c) == 0
        result.append({"r":r,"residue_polynomial":str(sp.factor(coef[r])),"residual":0})
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="gauss_stieltjes_results.json")
    args = parser.parse_args()
    mp.mp.dps = 75
    cases = [
        ("ordinary", mp.mpf(1), mp.mpf(1), mp.mpf(1)),
        ("central_binomial", mp.mpf("0.5"), mp.mpf("0.5"), mp.mpf(1)),
        ("shifted", mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf("0.8")),
        ("complex_parameters", mp.mpc("0.7", "0.2"), mp.mpc("1.2", "-0.1"), mp.mpf("0.8")),
    ]
    rows = []
    largest_error = mp.mpf(0)
    largest_stability = mp.mpf(0)
    for name, a, b, c in cases:
        first = numerical_series_jet(a, b, c, 70, 24)
        second = numerical_series_jet(a, b, c, 110, 32)
        rhs = closed_form_jet(a, b, c)
        for index in indices((1, 1, 2)):
            error = abs(second[index] - rhs[index])
            stability = abs(second[index] - first[index])
            largest_error = max(largest_error, error)
            largest_stability = max(largest_stability, stability)
            assert error < mp.mpf("1e-38"), (name, index, error)
            assert stability < mp.mpf("1e-30"), (name, index, stability)
            rows.append({
                "case": name,
                "taylor_index_a_b_s": list(index),
                "series_value": show(second[index]),
                "closed_form": show(rhs[index]),
                "absolute_residual": show(error),
                "change_on_tail_refinement": show(stability),
            })
        print(name, "completed", flush=True)
    # An independent ordinary integral detects the factor-two error in (41).
    # sum H_n^2 z^n = (Li_2(z)+log(1-z)^2)/(1-z), so beta integration gives
    # sum H_n^2/((n+1)(n+2)) = integral_0^1 [Li_2(z)+log(1-z)^2] dz.
    integral = mp.quad(lambda z: mp.polylog(2, z) + mp.log(1-z)**2, [0, mp.mpf("0.5"), 1])
    corrected = 1 + mp.zeta(2)
    assert abs(integral - corrected) < mp.mpf("1e-65")
    negative_first = central_negative_balance(70, 24)
    negative_second = central_negative_balance(110, 32)
    negative_expected = -mp.log(2) - mp.mpf("0.25")
    assert abs(negative_second - negative_expected) < mp.mpf("1e-50")
    assert abs(negative_second - negative_first) < mp.mpf("1e-35")
    report = {
        "working_decimal_digits": mp.mp.dps,
        "status": "All numerical and symbolic diagnostics passed.",
        "proof_status": "Proof is in sections/gauss_stieltjes.tex; numerical tail is not interval certified.",
        "series_acceleration": {"first": {"N":70,"K":24}, "second":{"N":110,"K":32}},
        "number_of_mixed_jet_checks": len(rows),
        "largest_absolute_residual": show(largest_error),
        "largest_refinement_change": show(largest_stability),
        "mixed_jet_checks": rows,
        "choi_equation_41_independent_integral": {
            "value": show(integral),
            "correct_value": show(corrected),
            "printed_value": show(2*corrected),
        },
        "symbolic_checks": symbolic_choi_checks(),
        "central_binomial_negative_balance": {
            "n_zero_bracket": "-3/4; W_0(-1)=0 by reciprocal-gamma continuation",
            "direct_series_with_tail": show(negative_second),
            "closed_form": show(negative_expected),
            "absolute_residual": show(abs(negative_second-negative_expected)),
            "change_on_tail_refinement": show(abs(negative_second-negative_first)),
        },
        "symbolic_residue_checks": symbolic_residue_checks(),
    }
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n")
    print("Largest residual:", mp.nstr(largest_error, 8))
    print("Largest refinement change:", mp.nstr(largest_stability, 8))
    print("Wrote", args.output)


if __name__ == "__main__":
    main()
