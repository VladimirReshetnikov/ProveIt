#!/usr/bin/env python3
"""Independent checks for the continuous-depth odd-lattice jet formulas.

The mathematical proofs are in lerch_lattice_jets.tex. Floating-point
comparisons below are diagnostics, not interval certificates or substitutes
for the analytic arguments. The negative-order Z jets are evaluated using
finite differences; positive-order F jets use Gamma-product integrals.
Neither side uses the reflection equation as an evaluation definition.
"""

from __future__ import annotations

import argparse
import functools
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


def bell(values):
    """Complete exponential Bell polynomials through len(values)."""
    out = [mp.mpf(1)]
    for n in range(1, len(values) + 1):
        out.append(mp.fsum(math.comb(n - 1, j - 1) * values[j - 1] * out[n - j]
                           for j in range(1, n + 1)))
    return out


def euler_sum(values):
    row = list(values)
    result = mp.mpc(0)
    for k in range(len(row)):
        result += row[0] / mp.power(2, k + 1)
        row = [row[j] - row[j + 1] for j in range(len(row) - 1)]
    return result


def reflected_jets(rho, N, terms):
    """Return Z_rho^{(depth r, order q)}(-N), r<=1, q<=2."""
    values = {(r, q): [] for r in range(2) for q in range(3)}
    poch = mp.mpf(1)
    harmonic = mp.mpc(0)
    for k in range(terms):
        if k:
            poch *= (rho + k - 1) / k
            harmonic += 1 / (rho + k - 1)
        a = k + rho / 2
        loga = mp.log(a)
        base = poch * a**N
        d = harmonic + N / (2 * a)
        values[0, 0].append(base)
        values[0, 1].append(-base * loga)
        values[0, 2].append(base * loga**2)
        values[1, 0].append(base * d)
        values[1, 1].append(base * (-loga * d - 1 / (2 * a)))
        values[1, 2].append(base * (loga**2 * d + loga / a))
    return {key: euler_sum(val) for key, val in values.items()}


def lattice_formula(rho, N, r, q, jets):
    n = N + 1
    L = mp.log(2 * mp.pi)
    cumulants = [L - mp.digamma(n)]
    if q >= 2:
        cumulants.append(mp.zeta(2) / 2 + mp.fsum(mp.mpf(k)**-2
                                               for k in range(1, N + 1)))
    bs = bell(cumulants[:q])
    C = (-1)**(N // 2) * mp.pi * (2 * mp.pi)**(rho + N - 1) / mp.factorial(N)
    def dz(j):
        return jets[0, j] if r == 0 else jets[1, j] + L * jets[0, j]
    return C * mp.fsum((-1)**j * math.comb(q, j) * bs[q - j] * dz(j)
                       for j in range(q + 1))


def gamma_moment_family(rho):
    """Cache special-function values across independent moment integrals."""
    prefactor = (2 * mp.pi)**(rho - 2) / mp.gamma(rho)
    psi_rho = mp.digamma(rho)
    L = mp.log(2 * mp.pi)

    @functools.lru_cache(maxsize=None)
    def base(x):
        zplus = rho / 2 + 1j * x / (2 * mp.pi)
        zminus = rho / 2 - 1j * x / (2 * mp.pi)
        b = prefactor * mp.gamma(zplus) * mp.gamma(zminus)
        arho = L - psi_rho + (mp.digamma(zplus) + mp.digamma(zminus)) / 2
        return b, arho

    def moment(N, r, q):
        n = N + 1
        psin = mp.digamma(n)
        psi1n = mp.polygamma(1, n)
        scale = mp.factorial(N)
        def integrand(x):
            if not x:
                return mp.mpf(0)
            b, arho = base(x)
            u = mp.log(x) - psin
            spectral = [mp.mpf(1), u, u*u - psi1n][q]
            return x**N * b / scale * (arho if r else 1) * spectral
        return mp.quad(integrand, [0, 1, 6, 24, mp.inf])
    return moment


def serialize_number(value, digits=45):
    if abs(mp.im(value)) < mp.mpf('1e-65'):
        return mp.nstr(mp.re(value), digits)
    return {"real": mp.nstr(mp.re(value), digits),
            "imag": mp.nstr(mp.im(value), digits)}


def exact_checks():
    v, t = sp.symbols('v t')
    cumulant_count = 0
    logsec = sp.series(-sp.log(sp.cos(sp.pi*v/2)), v, 0, 10).removeO()
    for N in range(0, 11, 2):
        n = N + 1
        for j in range(1, 9):
            raw = -sp.polygamma(j - 1, n)
            raw += sp.factorial(j) * logsec.coeff(v, j)
            if j == 1:
                raw += sp.log(2 * sp.pi)
                expected = sp.log(2 * sp.pi) + sp.EulerGamma - sp.harmonic(N)
            else:
                expected = sp.factorial(j - 1) * (
                    (1 - (1 + (-1)**j) * sp.Rational(1, 2)**j) * sp.zeta(j)
                    + (-1)**j * sp.harmonic(N, j))
            assert sp.simplify(raw - expected) == 0, (N, j, raw, expected)
            cumulant_count += 1

    finite_count = 0
    zero_count = 0
    for R in range(1, 6):
        heat = sp.series((2 * sp.cosh(t/2))**(-R), t, 0, 9).removeO()
        for N in range(9):
            degree = R + N - 1
            vals = [sp.rf(R, k) / sp.factorial(k)
                    * (k + sp.Rational(R, 2))**N
                    for k in range(degree + 3)]
            row = vals
            total = sp.S.Zero
            for k in range(len(vals)):
                if k > degree:
                    assert row[0] == 0
                total += row[0] * sp.Rational(1, 2)**(k + 1)
                row = [row[j] - row[j + 1] for j in range(len(row) - 1)]
            expected = (-1)**N * sp.factorial(N) * heat.coeff(t, N)
            assert sp.simplify(total - expected) == 0, (R, N, total, expected)
            finite_count += 1
            zero_count += N % 2

    # First two polylogarithm derivative formulas follow from the entire
    # depth-two germ, with gamma_q' left as independent formal variables.
    g0, g1, g2, ell = sp.symbols('g0 g1 g2 ell')
    E = -g0 + g1*v - g2*v*v/2
    product = sp.series(sp.exp(-ell*v) * E, v, 0, 3).removeO()
    assert sp.expand(product.coeff(v, 1) - (g1 + ell*g0)) == 0
    assert sp.expand(2*product.coeff(v, 2) - (-g2 - 2*ell*g1 - ell*ell*g0)) == 0
    return {"cumulants": cumulant_count,
            "finite_Euler_values": finite_count,
            "odd_trivial_zeros": zero_count,
            "polylogarithm_product_rules": 2}


def numerical_checks(terms, quick):
    mp.mp.dps = 90
    records = []
    depths = [mp.mpf('1.3'), mp.mpf(2)]
    if not quick:
        depths.append(mp.mpc('1.4', '0.2'))
    pairs = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)]
    for rho in depths:
        moments = gamma_moment_family(rho)
        for N in [0, 2]:
            # Guard digits account for cancellation in the finite differences.
            with mp.workdps(135):
                jets = reflected_jets(rho, N, terms)
            for r, q in pairs:
                predicted = lattice_formula(rho, N, r, q, jets)
                independent = moments(N, r, q)
                residual = abs(predicted - independent)
                relative = residual / max(mp.mpf(1), abs(independent))
                assert relative < mp.mpf('1e-45'), (rho, N, r, q, relative)
                record = {"rho": serialize_number(rho), "N": N,
                          "depth_derivative": r, "order_derivative": q,
                          "Gamma_integral": serialize_number(independent),
                          "Euler_reflection": serialize_number(predicted),
                          "relative_residual": mp.nstr(relative, 8)}
                records.append(record)
                print(json.dumps({"checked": len(records), "rho": record["rho"],
                                  "N": N, "r": r, "q": q,
                                  "relative_residual": record["relative_residual"]}),
                      flush=True)
    return records


def stieltjes_and_examples():
    mp.mp.dps = 60
    a = mp.mpf('0.5')
    gamma1prime = mp.diff(lambda z: mp.stieltjes(1, z), a)
    gamma2prime = mp.diff(lambda z: mp.stieltjes(2, z), a)
    E1prime = mp.diff(lambda w: w * mp.zeta(w + 1, a), mp.mpf(1))
    E1second = mp.diff(lambda w: w * mp.zeta(w + 1, a), mp.mpf(1), 2)
    assert abs(gamma1prime - E1prime) < mp.mpf('1e-50')
    assert abs(-gamma2prime - E1second) < mp.mpf('1e-50')
    Iprime_stieltjes = 2*mp.pi*gamma1prime - mp.pi**3*mp.log(2)
    Iprime_zeta = mp.pi**3 * (mp.euler + mp.log(mp.pi)
                             + mp.mpf(4)/3*mp.log(2)
                             + 12*mp.diff(mp.zeta, -1))
    Iprime_positive = mp.pi**3*(1 + mp.log(2)/3) + 6*mp.pi*mp.diff(mp.zeta, 2)
    assert abs(Iprime_stieltjes - Iprime_zeta) < mp.mpf('1e-48')
    assert abs(Iprime_stieltjes - Iprime_positive) < mp.mpf('1e-48')
    return {"gamma1_prime_half": serialize_number(gamma1prime),
            "gamma2_prime_half": serialize_number(gamma2prime),
            "I1_order_derivative_at_one": serialize_number(Iprime_stieltjes),
            "negative_zeta_comparison_residual": mp.nstr(abs(Iprime_stieltjes-Iprime_zeta), 8),
            "positive_zeta_comparison_residual": mp.nstr(abs(Iprime_stieltjes-Iprime_positive), 8)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--terms', type=int, default=230)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('lerch_lattice_verification.json'))
    args = parser.parse_args()
    exact = exact_checks()
    print(json.dumps({"exact_checks": exact}), flush=True)
    numerical = numerical_checks(args.terms, args.quick)
    examples = stieltjes_and_examples()
    record = {"status": "all assertions passed",
              "evidentiary_status": "Exact finite algebra and high-precision diagnostics; no interval certification.",
              "Euler_terms": args.terms,
              "Euler_decimal_precision": 135,
              "Gamma_integral_decimal_precision": 90,
              "exact_checks": exact, "numerical_checks": numerical,
              "Stieltjes_and_polylogarithm_examples": examples}
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({"status": record['status'], "output": str(args.output),
                      "numerical_count": len(numerical)}), flush=True)


if __name__ == '__main__':
    main()
