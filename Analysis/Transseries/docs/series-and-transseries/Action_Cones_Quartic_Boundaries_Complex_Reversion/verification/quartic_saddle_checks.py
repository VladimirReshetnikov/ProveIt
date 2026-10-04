#!/usr/bin/env python3
"""Reproduce focused checks of the quartic and ordinary saddle laws.

Run: python verification/quartic_saddle_checks.py
Outputs: quartic_saddle_results.json, quartic_saddle_table.tex, and
         ../figures/quartic_saddle_scaling.{pdf,png}.
Numerical checks are finite floating-point comparisons, not proofs of
asymptotic convergence and not interval arithmetic.
"""

from fractions import Fraction
import json
from pathlib import Path

import mpmath as mp

from verification import Gaussian, ONE, ZERO, decimal, setup_matplotlib


HERE = Path(__file__).resolve().parent
FIGURES = HERE.parent / "figures"
DEGREES = [50, 100, 200, 500, 1000, 2000]


def radius(p):
    return mp.sqrt(p * p + (1 - p) * (1 - p))


def phi(p, A, B):
    return (1 + mp.log(radius(p)) + p * mp.log(A) + (1 - p) * mp.log(B)
            - p * mp.log(p) - (1 - p) * mp.log(1 - p))


def phi_prime(p, A, B):
    return ((2 * p - 1) / (p * p + (1 - p) * (1 - p))
            + mp.log(A / B) + mp.log((1 - p) / p))


def phi_second(p):
    t = 2 * p - 1
    return -16 * t * t / ((1 + t * t) ** 2 * (1 - t * t))


def log_absolute_degree_sum(N, A, B, log_factorials):
    """Log-sum-exp evaluation of the exact defining finite sum."""
    terms = [
        (N - 1) * mp.log(abs(mp.mpc(n, N - n)))
        + n * mp.log(A) + (N - n) * mp.log(B)
        - log_factorials[n] - log_factorials[N - n]
        for n in range(N + 1)
    ]
    largest = max(terms)
    return largest + mp.log(mp.fsum(mp.exp(term - largest) for term in terms))


def exact_local_checks():
    # At critical symmetry, the coefficient of s^(2k) in Phi(1/2+s) is
    # 4^k/(2k) * ((-1)^(k+1) - 1/(2k-1)).
    coefficients = {
        2 * k: Fraction(4 ** k, 2 * k)
        * (Fraction((-1) ** (k + 1)) - Fraction(1, 2 * k - 1))
        for k in range(1, 5)
    }
    assert coefficients == {
        2: Fraction(0), 4: Fraction(-16, 3),
        6: Fraction(128, 15), 8: Fraction(-256, 7),
    }

    # Check the independently differentiated curvature formula exactly.
    for numerator in range(1, 20):
        p = Fraction(numerator, 20)
        q = 1 - p
        d = p * p + q * q
        t = 2 * p - 1
        differentiated = 2 / d - 2 * t * t / (d * d) - 1 / p - 1 / q
        compact = -16 * t * t / ((1 + t * t) ** 2 * (1 - t * t))
        assert differentiated == compact

    # All these critical-point calculations are Gaussian-rational.
    I = Gaussian(Fraction(0), Fraction(1))
    a = b = Gaussian(Fraction(1, 2), Fraction(-1, 2))
    w0 = a + b
    first_derivative = ONE + (-a) + (-(I * b))
    second_derivative = a + (-b)
    third_derivative = (-a) + I * b
    assert w0 == Gaussian(Fraction(1), Fraction(-1))
    assert first_derivative == ZERO
    assert second_derivative == ZERO
    assert third_derivative == I
    assert a.real * a.real + a.imag * a.imag == Fraction(1, 2)
    assert b.real * b.real + b.imag * b.imag == Fraction(1, 2)

    return {
        "critical_saddle_even_coefficients": {str(k): str(v) for k, v in coefficients.items()},
        "curvature_identity_rational_checks": 19,
        "cubic_critical_example": {
            "z0": "0", "a": "(1-i)/2", "b": "(1-i)/2", "w0": "1-i",
            "F_prime_at_zero": "0", "F_second_at_zero": "0",
            "F_third_at_zero": "i", "coefficient_moduli_squared": "1/2",
            "input_moduli_at_w0": "|a*exp(-w0)|=|b*exp(-i*w0)|=1/(e*sqrt(2))",
            "arithmetic": "exact Gaussian rationals",
        },
    }


def crossover_integral_limit(tau, eta):
    integral = 2 * mp.quad(
        lambda u: mp.exp(4 * tau * u * u - mp.mpf(16) / 3 * u ** 4)
        * mp.cosh(eta * u),
        [0, 1, 2, mp.inf],
    )
    return mp.sqrt(2) / mp.pi * integral


def crossover_scaled_sum(N, tau, eta, log_factorials):
    """N^(5/4) D_N / [2*e*q*cos(beta_N/2)]^N, with q cancelled."""
    beta = mp.pi / 2 + tau / mp.sqrt(N)
    delta = eta / mp.power(N, mp.mpf("0.75"))
    c, s = mp.cos(beta / 2), mp.sin(beta / 2)
    assert c > 0
    terms = []
    for n in range(N + 1):
        p = mp.mpf(n) / N
        r = mp.sqrt(c * c + s * s * (2 * p - 1) ** 2)
        terms.append(
            (N - 1) * mp.log(N * r) + delta * (n - mp.mpf(N) / 2)
            - log_factorials[n] - log_factorials[N - n]
            - N * (mp.log(2 * c) + 1)
        )
    largest = max(terms)
    return mp.exp(largest + mp.log(mp.fsum(mp.exp(v - largest) for v in terms))
                  + mp.mpf("1.25") * mp.log(N))


def crossover_checks(log_factorials, critical_A, critical_C):
    # Verify reduction to the original orthogonal, symmetric critical sum.
    direct = mp.exp(log_absolute_degree_sum(100, critical_A, critical_A, log_factorials)
                    + mp.mpf("1.25") * mp.log(100))
    reduced = crossover_scaled_sum(100, mp.mpf(0), mp.mpf(0), log_factorials)
    assert abs(direct - reduced) < mp.mpf("1e-90")
    assert abs(crossover_integral_limit(mp.mpf(0), mp.mpf(0)) - critical_C) < mp.mpf("1e-90")

    cases = []
    for tau_string, eta_string in [("0.4", "0.7"), ("-0.5", "0"), ("0", "1")]:
        tau, eta = mp.mpf(tau_string), mp.mpf(eta_string)
        limit = crossover_integral_limit(tau, eta)
        rows = []
        for N in [100, 500, 2000]:
            normalized = crossover_scaled_sum(N, tau, eta, log_factorials)
            ratio = normalized / limit
            assert mp.mpf("0.98") < ratio < mp.mpf("1.05")
            rows.append({"N": N, "normalized_sum": decimal(normalized),
                         "ratio_to_limit": decimal(ratio)})
        assert abs(mp.mpf(rows[-1]["ratio_to_limit"]) - 1) < mp.mpf("0.006")
        cases.append({"tau": tau_string, "eta": eta_string,
                      "limiting_integral_value": decimal(limit), "rows": rows})
    return {
        "angle": "beta_N=pi/2+tau/sqrt(N)",
        "tilt": "delta_N=eta/N^(3/4)",
        "amplitudes": "A=q*exp(delta_N/2), B=q*exp(-delta_N/2), q>0",
        "normalization": "N^(5/4)*D_N/[2*e*q*cos(beta_N/2)]^N",
        "limit": "sqrt(2)/pi * integral_R exp(4*tau*u^2+eta*u-16*u^4/3) du",
        "computation": "q cancelled algebraically before log-sum-exp evaluation",
        "orthogonal_symmetric_reduction_checked": True,
        "integral_at_zero_equals_C4_checked": True,
        "cases": cases,
    }


def compute_results():
    mp.mp.dps = 100
    log_factorials = [mp.loggamma(k + 1) for k in range(max(DEGREES) + 1)]
    critical_A = 1 / (mp.e * mp.sqrt(2))
    critical_C = 3 ** mp.mpf("0.25") * mp.gamma(mp.mpf("0.25")) / (2 * mp.sqrt(2) * mp.pi)

    A, B = mp.mpf("0.2"), mp.mpf("0.1")
    pstar = mp.findroot(lambda p: phi_prime(p, A, B), (mp.mpf("0.7"), mp.mpf("0.9")))
    assert abs(phi_prime(pstar, A, B)) < mp.mpf("1e-90")
    h = -phi_second(pstar)
    assert h > 0
    assert abs(h + mp.diff(lambda p: phi(p, A, B), pstar, 2)) < mp.mpf("1e-90")
    logR = phi(pstar, A, B)
    R = mp.exp(logR)
    C = 1 / (mp.sqrt(2 * mp.pi) * radius(pstar)
             * mp.sqrt(pstar * (1 - pstar)) * mp.sqrt(h))

    quartic_rows, ordinary_rows = [], []
    for N in DEGREES:
        logD = log_absolute_degree_sum(N, critical_A, critical_A, log_factorials)
        scaled = mp.exp(logD + mp.mpf("1.25") * mp.log(N))
        ratio = scaled / critical_C
        # Only finite numerical tolerances are asserted; no convergence
        # claim is inferred from observing a finite list of terms.
        assert mp.mpf("0.99") < ratio < mp.mpf("1.04")
        quartic_rows.append({"N": N, "D_N": decimal(mp.exp(logD)),
                             "scaled_D_N": decimal(scaled), "ratio_to_limit": decimal(ratio)})

        logD = log_absolute_degree_sum(N, A, B, log_factorials)
        scaled = mp.exp(logD - N * logR + mp.mpf("1.5") * mp.log(N))
        ratio = scaled / C
        assert mp.mpf("0.99") < ratio < mp.mpf("1.04")
        ordinary_rows.append({"N": N, "log_D_N": decimal(logD),
                              "scaled_D_N": decimal(scaled), "ratio_to_limit": decimal(ratio)})
    assert abs(mp.mpf(quartic_rows[-1]["ratio_to_limit"]) - 1) < mp.mpf("0.005")
    assert abs(mp.mpf(ordinary_rows[-1]["ratio_to_limit"]) - 1) < mp.mpf("0.001")

    return {
        "status": "all finite assertions passed",
        "precision_decimal_digits": mp.mp.dps,
        "numerical_status": "floating-point checks of finite values; not interval arithmetic or proof of convergence",
        "definition": "D_N=sum_{n=0}^N |n+i*(N-n)|^(N-1)*A^n*B^(N-n)/(n!*(N-n)!)",
        "method": "100-digit log-sum-exp with cached log-factorials",
        "exact_local_checks": exact_local_checks(),
        "uniform_quartic_crossover": crossover_checks(log_factorials, critical_A, critical_C),
        "quartic_saddle": {
            "A_and_B": "1/(e*sqrt(2))", "pstar": "1/2", "R": "1",
            "power": "N^(-5/4)",
            "constant_formula": "3^(1/4)*Gamma(1/4)/(2*sqrt(2)*pi)",
            "C": decimal(critical_C), "rows": quartic_rows,
        },
        "ordinary_saddle": {
            "A": "0.2", "B": "0.1", "pstar": decimal(pstar),
            "R": decimal(R), "minus_phi_second_at_pstar": decimal(h),
            "power": "R^N*N^(-3/2)",
            "constant_formula": "1/(sqrt(2*pi)*r(pstar)*sqrt(pstar*(1-pstar))*sqrt(-Phi''(pstar)))",
            "C": decimal(C), "rows": ordinary_rows,
        },
    }


def write_outputs(results):
    (HERE / "quartic_saddle_results.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    lines = [
        "% Generated by quartic_saddle_checks.py; finite floating-point checks.",
        r"\begin{tabular}{@{}rrr@{}}", r"\toprule",
        r"$N$ & Quartic: $D_NN^{5/4}/C_4$ & Ordinary: $D_NN^{3/2}/(C_2R^N)$ \\",
        r"\midrule",
    ]
    for qrow, orow in zip(results["quartic_saddle"]["rows"], results["ordinary_saddle"]["rows"]):
        qr = mp.nstr(mp.mpf(qrow["ratio_to_limit"]), 10)
        ordinary = mp.nstr(mp.mpf(orow["ratio_to_limit"]), 10)
        lines.append(rf"{qrow['N']} & {qr} & {ordinary} \\")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    (HERE / "quartic_saddle_table.tex").write_text("\n".join(lines), encoding="utf-8")

    lines = [
        "% Generated by quartic_saddle_checks.py; finite floating-point checks.",
        r"\begin{tabular}{@{}crrr@{}}", r"\toprule",
        r"$(\tau,\eta)$ & $N$ & Normalized sum & Ratio to limiting integral \\",
        r"\midrule",
    ]
    for case_index, case in enumerate(results["uniform_quartic_crossover"]["cases"]):
        for row_index, row in enumerate(case["rows"]):
            label = rf"$({case['tau']},{case['eta']})$" if row_index == 0 else ""
            scaled = mp.nstr(mp.mpf(row["normalized_sum"]), 10)
            ratio = mp.nstr(mp.mpf(row["ratio_to_limit"]), 10)
            lines.append(rf"{label} & {row['N']} & {scaled} & {ratio} \\")
        if case_index < 2:
            lines.append(r"\addlinespace")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    (HERE / "quartic_crossover_table.tex").write_text("\n".join(lines), encoding="utf-8")

    plt = setup_matplotlib()
    fig, axes = plt.subplots(1, 2, figsize=(7.1, 2.8))
    configurations = [
        ("quartic_saddle", "Quartic saddle", r"$D_N N^{5/4}/C_4$", "#16617c"),
        ("ordinary_saddle", "Ordinary saddle", r"$D_N N^{3/2}/(C_2R^N)$", "#aa6439"),
    ]
    for ax, (key, title, ylabel, color) in zip(axes, configurations):
        xx = [row["N"] for row in results[key]["rows"]]
        yy = [float(row["ratio_to_limit"]) for row in results[key]["rows"]]
        ax.axhline(1, color="#697c86", ls=(0, (3, 3)), lw=0.8)
        ax.plot(xx, yy, "o-", color=color, ms=4.2, lw=1.15, markeredgewidth=0)
        ax.set_xscale("log")
        ax.set_xticks([50, 100, 500, 2000], ["50", "100", "500", "2000"])
        ax.set_xlabel("Total degree $N$")
        ax.set_ylabel(ylabel)
        ax.set_title(title, loc="left", pad=10)
        ax.set_ylim(0.999, max(yy) + 0.002)
        ax.grid(axis="y", color="#e1e7ea", lw=0.6)
        ax.tick_params(which="both", length=3, width=0.6, colors="#3a4d57")
        for spine in ["left", "bottom"]:
            ax.spines[spine].set_color("#aab7be")
    fig.subplots_adjust(left=0.085, right=0.985, top=0.86, bottom=0.19, wspace=0.37)
    FIGURES.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIGURES / "quartic_saddle_scaling.pdf", bbox_inches="tight", pad_inches=0.04)
    fig.savefig(FIGURES / "quartic_saddle_scaling.png", dpi=300, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


if __name__ == "__main__":
    data = compute_results()
    write_outputs(data)
    print("All finite assertions passed.")
    print("Quartic constant:", data["quartic_saddle"]["C"])
    print("Ordinary p*, R, C:", data["ordinary_saddle"]["pstar"],
          data["ordinary_saddle"]["R"], data["ordinary_saddle"]["C"])
    for q, o in zip(data["quartic_saddle"]["rows"], data["ordinary_saddle"]["rows"]):
        print(q["N"], "quartic ratio", q["ratio_to_limit"], "ordinary ratio", o["ratio_to_limit"])
    for case in data["uniform_quartic_crossover"]["cases"]:
        print("Crossover tau, eta, limit:", case["tau"], case["eta"], case["limiting_integral_value"])
        for row in case["rows"]:
            print("  N =", row["N"], "ratio =", row["ratio_to_limit"])
