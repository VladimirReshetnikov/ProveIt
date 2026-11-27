#!/usr/bin/env python3
"""Reproduce finite checks and parameter tables for the research report.

The proof is analytic. These high-precision calculations independently check
its constants and selected parameter values; they are not a replacement for
the proof and are not interval-certified numerical zero computations.
"""
from pathlib import Path
import json
from math import comb, factorial
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 80
ROOT = Path(__file__).resolve().parents[1]


def text(x, digits=28):
    return mp.nstr(x, digits)


def parameters(Q):
    Q = mp.mpf(Q)
    assert Q >= 3
    L = mp.log(2 * Q)
    X = int(mp.ceil(12_000_000 * L * L))
    h = mp.mpf(1) / (64 * X)
    D = 1 + mp.log(2 * Q * (256 * X + 2))
    Z = 160 * mp.sqrt(X) * D
    m = 2 * int(mp.ceil(max(mp.mpf(8), 2 * mp.log(Z) / mp.log(3)) / 2))
    H = 256 * m * X
    return Q, L, X, h, D, Z, m, H


def tail_bound(X, h, m, H, A, B):
    H = mp.mpf(H)
    return (A * mp.sqrt(X) / mp.log(2) * h * m * (H + 1)
            * (4 * m / (3 * h * H)) ** m
            * (mp.log(B * (H + 2)) / (m - 1) + mp.mpf(1) / (m - 1) ** 2))


def central_density_times_h(m):
    """Exact B-spline central density f(0)*h for even m."""
    assert m % 2 == 0 and m >= 2
    s = sum((-1) ** j * comb(m, j) * (m - 2*j) ** (m-1)
            for j in range(m//2 + 1))
    return Fraction(m * s, 2**m * factorial(m-1))


def main():
    scalar = {
        "Euler_series_upper_bound": (mp.mpf(7)/12 * mp.log(2) + mp.mpf(2)/9) / mp.sqrt(2),
        "seven_e_over_eight_pi": 7 * mp.e / (8 * mp.pi),
        "zeta_pole_max_at_m8": mp.pi/64,
        "global_separation_coefficient_lower": 5 * mp.log(2) / (128 * mp.pi * mp.sqrt(13_000_000)),
    }
    assert scalar["Euler_series_upper_bound"] < mp.mpf('0.5')
    assert scalar["seven_e_over_eight_pi"] < 1
    assert scalar["zeta_pole_max_at_m8"] < mp.mpf(1)/16
    assert scalar["global_separation_coefficient_lower"] > mp.mpf('0.000001')

    # The paper proves that this ratio decreases; check its largest endpoint.
    L = mp.log(6)
    x = 1_000_000 * L**2
    contradiction_ratio = (mp.mpf('47.5') * L + 89 + mp.mpf('1.5') * (1 + mp.log(x))**2) / L
    assert contradiction_ratio < 333 < 1000
    rows = []
    for q in [3, 5, 10, 100, 1000, 10**6, 10**12]:
        Q, L, X, h, D, Z, m, H = parameters(q)
        assert m*m <= 3 ** (m//2)
        assert mp.power(3, m//2) >= Z
        tails = [tail_bound(X, h, m, k*H, mp.mpf(2), 2*Q) for k in [1, 2, 10]]
        assert tails[2] <= tails[1] <= tails[0] <= mp.mpf(1)/8
        simplified_tail = 20 * mp.sqrt(X) * D * m*m * mp.power(3, -m)
        assert tails[0] <= simplified_tail <= mp.mpf(1)/8
        gamma_bound = 4*h/mp.log(2)
        pole_bound = 32*mp.pi*X/H
        assert gamma_bound <= mp.mpf(1)/16 and pole_bound <= mp.mpf(1)/16
        delta = 5*mp.log(2)*H/(128*mp.pi*mp.sqrt(X))
        assert delta > H/(1_000_000 * L)
        rows.append({
            "Q": q, "X_Q": X, "m_Q": m, "H_Q": H,
            "Delta_Q_at_H_Q": text(delta),
            "explicit_tail_H_Q": text(tails[0]),
            "simplified_tail": text(simplified_tail),
            "tail_twice_H_Q": text(tails[1]),
            "tail_ten_times_H_Q": text(tails[2]),
            "gamma_bound": text(gamma_bound), "pole_bound": text(pole_bound),
        })
    density_cases = []
    for m in range(2, 42, 2):
        c = central_density_times_h(m)
        assert c >= 1
        density_cases.append({"m": m, "f0_times_h_exact": str(c)})
    out = {
        "status": "all_checks_passed",
        "scope": "finite high-precision checks; analytic proofs remain in report.tex",
        "precision_decimal_digits": mp.mp.dps,
        "scalar_checks": {k: text(v) for k, v in scalar.items()},
        "angular_contradiction_RHS_over_log6": text(contradiction_ratio),
        "parameter_rows": rows, "exact_B_spline_checks": density_cases,
    }
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'constants.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({"status": out['status'], "parameter_cases": len(rows),
                      "exact_density_cases": len(density_cases),
                      "q5_parameters": rows[1]}, indent=2))


if __name__ == '__main__':
    main()
