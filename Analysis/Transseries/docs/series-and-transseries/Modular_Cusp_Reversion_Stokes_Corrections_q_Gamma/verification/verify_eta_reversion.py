#!/usr/bin/env python3
"""Exact coefficient and numerical checks for eta-cusp series reversion.

All formal coefficients are rational and computed without floating point.
Numerical experiments support, but do not prove, identities or error bounds.
Requires Python 3, mpmath, numpy, matplotlib.
"""
from fractions import Fraction as F
from pathlib import Path
import csv
import json
import math
import mpmath as mp

HERE = Path(__file__).resolve().parent
ORDER = 14


def sigma1(n):
    return sum(d for d in range(1, n + 1) if n % d == 0)


def euler_product_coefficients(exponents, order):
    """Coefficients of product_d P(z^d)^exponents[d] via logarithmic derivative."""
    coeff = [F(1)] + [F(0)] * order
    log_deriv = [F(0)] + [
        F(-sum(e * d * sigma1(n // d)
               for d, e in exponents.items() if n % d == 0))
        for n in range(1, order + 1)
    ]
    for n in range(1, order + 1):
        coeff[n] = sum(log_deriv[j] * coeff[n - j]
                       for j in range(1, n + 1)) / n
    return coeff


def direct_euler_coefficients(exponents, order):
    """Independent truncated multiplication of all relevant Euler factors."""
    out = [F(1)] + [F(0)] * order
    for d, exponent in exponents.items():
        for n in range(1, order // d + 1):
            step = d * n
            factor = [F(0)] * (order + 1)
            factor[0] = F(1)
            binom = F(1)
            for k in range(1, order // step + 1):
                binom *= F(exponent - k + 1, k)
                factor[step * k] = (-1) ** k * binom
            out = multiply(out, factor, order)
    return out


def multiply(a, b, order):
    out = [F(0)] * (order + 1)
    for i, x in enumerate(a[:order + 1]):
        for j, y in enumerate(b[:order + 1 - i]):
            out[i + j] += x * y
    return out


def compose(a, b, order):
    out = [F(0)] * (order + 1)
    power = [F(1)] + [F(0)] * order
    for c in a[:order + 1]:
        out = [x + c * y for x, y in zip(out, power)]
        power = multiply(power, b, order)
    return out


def power_one_plus(a, exponent, order):
    assert a[0] == 1
    u = list(a[:order + 1]) + [F(0)] * max(0, order + 1 - len(a))
    u[0] = F(0)
    out = [F(1)] + [F(0)] * order
    power = [F(1)] + [F(0)] * order
    binom = F(1)
    for k in range(1, order + 1):
        power = multiply(power, u, order)
        binom *= (exponent - (k - 1)) / k
        out = [x + binom * y for x, y in zip(out, power)]
    return out


def minus_log_one_plus(a, order):
    assert a[0] == 1
    u = list(a[:order + 1]) + [F(0)] * max(0, order + 1 - len(a))
    u[0] = F(0)
    out = [F(0)] * (order + 1)
    power = [F(1)] + [F(0)] * order
    for k in range(1, order + 1):
        power = multiply(power, u, order)
        c = F((-1) ** k, k)
        out = [x + c * y for x, y in zip(out, power)]
    return out


def rational_string(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


R_coeff = euler_product_coefficients({2: 3, 3: -4, 6: 1}, ORDER + 2)
assert R_coeff == direct_euler_coefficients({2: 3, 3: -4, 6: 1}, ORDER + 2)
Y_coeff = [-c for c in R_coeff]
Y_coeff[0] = F(0)
assert Y_coeff[1] == 0 and Y_coeff[2] == 3
H_coeff = [y / 3 for y in Y_coeff[2:]]
Q_coeff = [F(0)] + [
    power_one_plus(H_coeff, F(-n, 2), n - 1)[n - 1] / n
    for n in range(1, ORDER + 1)
]
denominator_coeff = minus_log_one_plus(Q_coeff[1:], ORDER - 1)
inverse_residual = compose(Y_coeff, Q_coeff, ORDER + 1)
assert inverse_residual[0:2] == [0, 0]
assert inverse_residual[2] == 3
assert not any(inverse_residual[3:])

ordinary_coeff = euler_product_coefficients({1: 1, 2: -5, 3: 5, 6: -1}, ORDER)
assert ordinary_coeff == direct_euler_coefficients({1: 1, 2: -5, 3: 5, 6: -1}, ORDER)
ordinary_m = {1: -1, 2: 5, 3: -5, 6: 1}
assert sum(ordinary_m.values()) == 0
assert sum(F(m, d) for d, m in ordinary_m.items()) == 0
assert sum(d * m for d, m in ordinary_m.items()) == 0
ordinary_y = [F(0)] + [-c for c in ordinary_coeff[1:]]
ordinary_inverse = [F(0)] + [
    power_one_plus(ordinary_y[1:], F(-n), n - 1)[n - 1] / n
    for n in range(1, ORDER + 1)
]
assert compose(ordinary_y, ordinary_inverse, ORDER) == [F(0), F(1)] + [F(0)] * (ORDER - 1)

balanced_families = {}
balanced_family_inverse = {}
for m in range(1, 8):
    g = math.gcd(m, 3)
    exponents = {m + j: (-1) ** j * math.comb(3, j) * (m + j) // g for j in range(4)}
    assert sum(exponents.values()) == 0
    assert sum(d * e for d, e in exponents.items()) == 0
    assert sum(F(e, d) for d, e in exponents.items()) == 0
    L = math.lcm(*exponents)
    original_exponents = {L // d: e for d, e in exponents.items()}
    assert math.gcd(*original_exponents) == 1
    assert sum(original_exponents.values()) == 0
    assert sum(d * e for d, e in original_exponents.items()) == 0
    assert sum(F(e, d) for d, e in original_exponents.items()) == 0
    coeffs = euler_product_coefficients(exponents, ORDER + m + 1)
    assert all(c == 0 for c in coeffs[1:m]) and coeffs[m] == -m // g
    a = m // g
    ym = [F(0)] + [-c / a for c in coeffs[1:]]
    hm = ym[m:]
    im = [F(0)] + [power_one_plus(hm, F(-n, m), n - 1)[n - 1] / n
                     for n in range(1, ORDER + 1)]
    cm = compose(ym, im, ORDER + m - 1)
    assert cm[m] == 1 and all(c == 0 for n, c in enumerate(cm) if n != m)
    balanced_family_inverse[m] = im
    balanced_families[m] = {"dual_exponents": exponents, "original_exponents": original_exponents,
                            "L": L, "ramification": m, "leading_defect_coefficient": m // g,
                            "dual_coefficients": [rational_string(c) for c in coeffs],
                            "inverse_Q_of_s_coefficients": [rational_string(c) for c in im],
                            "exact_inverse_composition_checked_through_degree": ORDER + m - 1}

qgamma_coefficients = {}
for k in [2, 3, 4]:
    Ak = euler_product_coefficients({1: k, k: -1}, ORDER + 1)
    assert Ak == direct_euler_coefficients({1: k, k: -1}, ORDER + 1)
    if k == 2:
        for n, c in enumerate(Ak):
            root = math.isqrt(n)
            expected = F(1) if n == 0 else F(2 * (-1) ** root) if root * root == n else F(0)
            assert c == expected
    yk = [F(0)] + [-c / k for c in Ak[1:]]
    assert yk[1] == 1
    hk = yk[1:]
    inv = [F(0)] + [power_one_plus(hk, F(-n), n - 1)[n - 1] / n
                     for n in range(1, ORDER + 1)]
    lg = minus_log_one_plus(inv[1:], ORDER - 1)
    ck = compose(yk, inv, ORDER)
    assert ck[0] == 0 and ck[1] == 1 and not any(ck[2:])
    qgamma_coefficients[k] = {"product": Ak, "inverse": inv, "log_correction": lg}

symbolic = {
    "balanced_R_coefficients_indexed_from_zero": [rational_string(c) for c in R_coeff],
    "balanced_Y_coefficients_indexed_from_zero": [rational_string(c) for c in Y_coeff],
    "inverse_Q_of_s_coefficients_indexed_from_zero": [rational_string(c) for c in Q_coeff],
    "log_denominator_correction_coefficients_indexed_from_zero": [rational_string(c) for c in denominator_coeff],
    "ordinary_transformed_product_coefficients_indexed_from_zero": [rational_string(c) for c in ordinary_coeff],
    "ordinary_transform_constant": "9/8",
    "ordinary_inverse_coefficients_indexed_from_zero": [rational_string(c) for c in ordinary_inverse],
    "primitive_arbitrary_ramification_families": balanced_families,
    "inverse_composition_verified_through_degree": ORDER + 1,
    "qgamma_multiplication_products": {
        str(k): {key: [rational_string(c) for c in values] for key, values in record.items()}
        for k, record in qgamma_coefficients.items()
    },
}
(HERE / "exact_coefficients.json").write_text(json.dumps(symbolic, indent=2) + "\n")


mp.mp.dps = 360
C = 2 * mp.pi ** 2 / 3


def P(z):
    return mp.qp(z, z)


def eta_scaled(t, d):
    return mp.exp(-d * t / 24) * P(mp.exp(-d * t))


def F_original(t):
    return 3 * mp.sqrt(3) / 4 * eta_scaled(t, 1) * eta_scaled(t, 3) ** 3 / eta_scaled(t, 2) ** 4


def R_dual(Q):
    return P(Q ** 6) * P(Q ** 2) ** 3 / P(Q ** 3) ** 4


def ordinary_original(t):
    return mp.fprod(P(mp.exp(-d * t)) ** m for d, m in ordinary_m.items())


def ordinary_dual(t):
    Q = mp.exp(-C / t)
    return mp.mpf(9) / 8 * P(Q) * P(Q ** 3) ** 5 / (P(Q ** 2) ** 5 * P(Q ** 6))


def polynomial(coefficients, z, degree):
    return mp.fsum(mp.mpf(c.numerator) / c.denominator * z ** n
                   for n, c in enumerate(coefficients[:degree + 1]))


def number(z):
    if isinstance(z, mp.mpc):
        return {"real": mp.nstr(z.real, 80), "imag": mp.nstr(z.imag, 80)}
    return mp.nstr(z, 80)


rows = []
numerics = []
for t in [mp.mpf("0.8"), mp.mpf("0.5"), mp.mpf("0.3"), mp.mpc("0.5", "0.15")]:
    Q = mp.exp(-C / t)
    original = F_original(t)
    dual = R_dual(Q)
    assert abs(original - dual) < mp.mpf("1e-340")
    assert abs(ordinary_original(t) - ordinary_dual(t)) < mp.mpf("1e-340")
    Y = 1 - original
    s = mp.sqrt(Y / 3)
    # Pick the square-root branch agreeing with Q near this cusp point.
    if abs(s - Q) > abs(-s - Q):
        s = -s
    item = {"t": number(t), "Q": number(Q), "Y": number(Y),
            "modular_identity_absolute_error": number(abs(original - dual)),
            "ordinary_modular_identity_absolute_error": number(abs(ordinary_original(t) - ordinary_dual(t))),
            "inverse_truncations": []}
    for degree in [2, 4, 6, 8, 10, 12]:
        Qn = polynomial(Q_coeff, s, degree)
        # Recover the logarithm branch represented by the prescribed t.
        principal_log = -mp.log(Qn)
        winding = mp.nint(((C / t) - principal_log).imag / (2 * mp.pi))
        tn = C / (principal_log + 2j * mp.pi * winding)
        if abs(tn.imag) < mp.mpf("1e-150"):
            tn = tn.real
        rQ = abs(Qn - Q)
        rt = abs(tn - t)
        residual = abs(1 - R_dual(Qn) - Y)
        item["inverse_truncations"].append({"degree": degree, "Q_error": number(rQ), "t_error": number(rt),
                                              "Y_composition_residual": number(residual)})
        rows.append([mp.nstr(t, 20), degree, mp.nstr(abs(s), 30), mp.nstr(rQ, 30), mp.nstr(rt, 30), mp.nstr(residual, 30)])
    negative_root = mp.findroot(lambda z: 1 - R_dual(z) - Y, (-s * mp.mpf("0.9"), -s * mp.mpf("1.1")),
                                solver="secant", tol=mp.mpf("1e-330"), verify=True)
    negative_t = C / (-mp.log(negative_root))
    negative_identity_error = abs(F_original(negative_t) - original)
    assert negative_identity_error < mp.mpf("1e-310")
    item["negative_root_branch"] = {"exact_Q_root": number(negative_root), "principal_log_t": number(negative_t),
                                    "original_F_identity_absolute_error": number(negative_identity_error),
                                    "inverse_truncations": []}
    for degree in [4, 8, 10, 12]:
        Qn = polynomial(Q_coeff, -s, degree)
        tn = C / (-mp.log(Qn))
        item["negative_root_branch"]["inverse_truncations"].append({
            "degree": degree, "Q_error": number(abs(Qn - negative_root)), "t_error": number(abs(tn - negative_t)),
            "Y_composition_residual": number(abs(1 - R_dual(Qn) - Y))})
    numerics.append(item)
(HERE / "high_precision_checks.json").write_text(json.dumps({"decimal_precision": mp.mp.dps, "cases": numerics}, indent=2) + "\n")
with (HERE / "inverse_errors.csv").open("w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["t", "Q_series_degree", "abs_s", "absolute_Q_error", "absolute_t_error", "absolute_Y_residual"])
    writer.writerows(rows)

qgamma_numerics = []
for k in [2, 3, 4]:
    for t in [mp.mpf("1"), mp.mpf("2"), mp.mpc("2", "0.3")]:
        q = mp.exp(-t)
        Q = mp.exp(-4 * mp.pi ** 2 / t)
        original = mp.fprod(mp.qgamma(mp.mpf(r) / k, q) for r in range(1, k))
        factor = (mp.power(k, -mp.mpf("0.5"))
                  * mp.power(2 * mp.pi * (1 - q) / t, mp.mpf(k - 1) / 2)
                  * mp.exp((mp.mpf(k) - 1 / mp.mpf(k)) * t / 24))
        normalized = original / factor
        dual = P(Q) ** k / P(Q ** k)
        assert abs(normalized - dual) < mp.mpf("1e-340")
        y = (1 - normalized) / k
        record = {"k": k, "t": number(t), "normalized_value": number(normalized), "Q": number(Q),
                  "identity_absolute_error": number(abs(normalized - dual)), "inverse_truncations": []}
        for degree in [4, 8, 12]:
            Qn = polynomial(qgamma_coefficients[k]["inverse"], y, degree)
            principal_log = -mp.log(Qn)
            winding = mp.nint(((4 * mp.pi ** 2 / t) - principal_log).imag / (2 * mp.pi))
            tn = 4 * mp.pi ** 2 / (principal_log + 2j * mp.pi * winding)
            record["inverse_truncations"].append({"degree": degree, "Q_error": number(abs(Qn - Q)),
                                                  "t_error": number(abs(tn - t))})
        qgamma_numerics.append(record)
(HERE / "qgamma_checks.json").write_text(json.dumps({"decimal_precision": mp.mp.dps, "cases": qgamma_numerics}, indent=2) + "\n")

arbitrary_ramification_checks = []
for m in [2, 3, 4]:
    family = balanced_families[m]
    e = family["dual_exponents"]
    original_e = family["original_exponents"]
    A = 4 * mp.pi ** 2 / family["L"]
    constant = mp.fprod(mp.power(d, mp.mpf(exponent) / 2) for d, exponent in e.items())
    for w in [mp.mpf("10"), mp.mpc("10", "2")]:
        t = A / w
        Q = mp.exp(-w)
        original = mp.fprod(P(mp.exp(-d * t)) ** exponent for d, exponent in original_e.items())
        normalized = original / constant
        dual = mp.fprod(P(Q ** d) ** exponent for d, exponent in e.items())
        assert abs(normalized - dual) < mp.mpf("1e-335")
        y = (1 - normalized) / family["leading_defect_coefficient"]
        s0 = mp.root(y, m)
        candidates = [s0 * mp.exp(2j * mp.pi * j / m) for j in range(m)]
        branch = min(range(m), key=lambda j: abs(candidates[j] - Q))
        s = candidates[branch]
        record = {"m": m, "L": family["L"], "t": number(t), "Q": number(Q),
                  "multiplicative_constant": number(constant), "selected_root_of_unity_index": branch,
                  "identity_absolute_error": number(abs(normalized - dual)), "inverse_truncations": []}
        for degree in [4, 8, 12]:
            Qn = polynomial(balanced_family_inverse[m], s, degree)
            principal_log = -mp.log(Qn)
            winding = mp.nint((w - principal_log).imag / (2 * mp.pi))
            tn = A / (principal_log + 2j * mp.pi * winding)
            record["inverse_truncations"].append({"degree": degree, "Q_error": number(abs(Qn - Q)),
                                                  "t_error": number(abs(tn - t))})
        arbitrary_ramification_checks.append(record)
(HERE / "arbitrary_ramification_checks.json").write_text(json.dumps(
    {"decimal_precision": mp.mp.dps, "cases": arbitrary_ramification_checks}, indent=2) + "\n")


def draw_plot():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np
    plt.rcParams.update({"font.size": 11, "axes.spines.top": False, "axes.spines.right": False,
                         "figure.dpi": 150, "savefig.dpi": 200})
    ts = np.linspace(0.7, 2.0, 56)
    fig, ax = plt.subplots(figsize=(7.2, 4.1))
    for degree, color in [(2, "#b65438"), (4, "#ad8b26"), (6, "#28786d"), (8, "#345fa5")]:
        errors = []
        for real_t in ts:
            t = mp.mpf(str(real_t))
            Q = mp.exp(-C / t)
            s = mp.sqrt((1 - R_dual(Q)) / 3)
            Qn = polynomial(Q_coeff, s, degree)
            tn = C / (-mp.log(Qn))
            errors.append(float(abs(tn - t)))
        ax.semilogy(ts, errors, label=f"Degree {degree}", color=color, linewidth=1.7)
    ax.set_xlabel(r"Original real parameter $t$")
    ax.set_ylabel(r"Absolute inverse error $|t_N-t|$")
    ax.set_title("Balanced eta cusp: convergence of the inverse expansion", loc="left", fontsize=12, pad=12)
    ax.grid(True, axis="y", which="major", alpha=0.18)
    ax.legend(frameon=False, ncol=2, loc="lower right")
    fig.tight_layout()
    fig.savefig(HERE / "eta_inverse_convergence.pdf")
    fig.savefig(HERE / "eta_inverse_convergence.png")
    plt.close(fig)


draw_plot()
print("R coefficients:", ", ".join(rational_string(c) for c in R_coeff[:13]))
print("Q coefficients:", ", ".join(rational_string(c) for c in Q_coeff[:13]))
print("log denominator correction:", ", ".join(rational_string(c) for c in denominator_coeff[:11]))
print("ordinary dual coefficients:", ", ".join(rational_string(c) for c in ordinary_coeff[:13]))
for k, record in qgamma_coefficients.items():
    print("qgamma k =", k)
    for key, coeffs in record.items():
        print(" ", key, ", ".join(rational_string(c) for c in coeffs[:14]))
for item in numerics:
    print("t =", item["t"], "; identity error =", item["modular_identity_absolute_error"])
    for truncation in item["inverse_truncations"]:
        if truncation["degree"] in [4, 8, 10]:
            print("  degree", truncation["degree"], "t error", truncation["t_error"])
