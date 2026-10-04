#!/usr/bin/env python3
"""Reproduce root-of-unity cusp phases and one rigorous rational disk bound.

Numerical checks use 80 decimal digits. The disk inequality is verified
exactly with Fraction arithmetic; its certificate does not depend on the
floating-point experiments. All output paths are relative to this script.
"""
from fractions import Fraction
from pathlib import Path
from math import gcd, lcm
import json
import mpmath as mp

HERE = Path(__file__).resolve().parent
mp.mp.dps = 80


def rational_text(q):
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def to_mp(q):
    if isinstance(q, Fraction):
        return mp.mpf(q.numerator) / q.denominator
    return mp.mpf(q)


def number(z):
    if isinstance(z, mp.mpc):
        return {"real": mp.nstr(z.real, 60), "imag": mp.nstr(z.imag, 60)}
    return mp.nstr(z, 60)


def sawtooth_fraction(n, k):
    residue = n % k
    return Fraction(0) if residue == 0 else Fraction(residue, k) - Fraction(1, 2)


def dedekind_sum(h, k):
    """s(h,k) as an exact rational, with the standard sawtooth convention."""
    if k < 1 or gcd(h, k) != 1:
        raise ValueError("Require k >= 1 and gcd(h,k) = 1")
    return sum((sawtooth_fraction(n, k) * sawtooth_fraction(h * n, k)
                for n in range(1, k)), Fraction(0))


def P(q):
    assert abs(q) < 1
    return mp.qp(q, q)


def cusp_phase(h, k):
    """Phase of the transformed nome: exp(-2*pi*i*h_inverse/k)."""
    if k == 1:
        return mp.mpf(1)
    return mp.exp(-2j * mp.pi * pow(h % k, -1, k) / k)


def single_cusp_transform(h, k, t):
    s = dedekind_sum(h, k)
    transformed_nome = cusp_phase(h, k) * mp.exp(-4 * mp.pi ** 2 / (k * k * t))
    prefactor = (mp.exp(-1j * mp.pi * to_mp(s)) * mp.sqrt(2 * mp.pi / (k * t))
                 * mp.exp(-mp.pi ** 2 / (6 * k * k * t) + t / 24))
    return prefactor * P(transformed_nome)


assert dedekind_sum(1, 2) == 0
assert dedekind_sum(1, 3) == Fraction(1, 18)
assert dedekind_sum(2, 5) == 0
assert dedekind_sum(1, 7) == Fraction(5, 14)
for h, k in [(2, 3), (3, 7), (5, 12), (8, 13)]:
    # Independent exact phase convention check through reciprocity.
    reciprocity = dedekind_sum(h, k) + dedekind_sum(k, h)
    assert reciprocity == -Fraction(1, 4) + (Fraction(h, k) + Fraction(k, h) + Fraction(1, h * k)) / 12

single_checks = []
for h, k in [(0, 1), (1, 2), (1, 3), (2, 5), (3, 7), (5, 12), (-1, 7), (8, 13)]:
    for t in [mp.mpf("0.7"), mp.mpc("0.4", "0.17"), mp.mpc("0.9", "-0.33")]:
        q = mp.exp(2j * mp.pi * h / k - t)
        direct = P(q)
        transformed = single_cusp_transform(h, k, t)
        error = abs(direct - transformed)
        relative = error / max(mp.mpf(1), abs(direct))
        assert relative < mp.mpf("1e-65")
        single_checks.append({"h": h, "k": k, "t": number(t),
                              "dedekind_sum": rational_text(dedekind_sum(h, k)),
                              "absolute_error": number(error), "scaled_error": number(relative)})


def product_transform(exponents, h, k, t):
    """General finite product, retaining every multiplier and cusp phase."""
    L = lcm(*exponents)
    W = sum(exponents.values())
    T = sum(d * e for d, e in exponents.items())
    I = Fraction(0)
    S = Fraction(0)
    constant = mp.mpf(1)
    dual = mp.mpf(1)
    nome = mp.exp(-4 * mp.pi ** 2 / (k * k * L * t))
    records = []
    for d, e in exponents.items():
        g = gcd(d, k)
        kd = k // g
        hd = (h * (d // g)) % kd if kd > 1 else 0
        sd = dedekind_sum(hd, kd)
        lam = L * g * g // d
        assert lam * d == L * g * g
        I += Fraction(e * g * g, d)
        S += e * sd
        constant *= mp.power(kd * d, -mp.mpf(e) / 2)
        dual *= P(cusp_phase(hd, kd) * nome ** lam) ** e
        records.append({"d": d, "exponent": e, "reduced_h": hd, "reduced_k": kd,
                        "dual_nome_power": lam, "dedekind_sum": rational_text(sd)})
    prefactor = (mp.power(2 * mp.pi / t, mp.mpf(W) / 2) * constant
                 * mp.exp(-mp.pi ** 2 * to_mp(I) / (6 * k * k * t)
                          + T * t / 24 - 1j * mp.pi * to_mp(S)))
    return prefactor * dual, {"L": L, "W": W, "T": T, "cusp_I": rational_text(I),
                              "dedekind_phase_sum": rational_text(S), "factor_data": records}


product_checks = []
products = {
    "level_six_raw_balanced": {1: -1, 2: 5, 3: -5, 6: 1},
    "eta_baseline_Euler_part": {1: 1, 2: -4, 3: 3},
    "primitive_ramification_three": {20: 1, 15: -4, 12: 5, 10: -2},
}
for name, exponents in products.items():
    for h, k in [(1, 2), (1, 3), (2, 5), (3, 7)]:
        for t in [mp.mpf("0.15"), mp.mpc("0.15", "0.04")]:
            q = mp.exp(2j * mp.pi * h / k - t)
            direct = mp.fprod(P(q ** d) ** e for d, e in exponents.items())
            transformed, data = product_transform(exponents, h, k, t)
            error = abs(direct - transformed)
            relative = error / max(mp.mpf(1), abs(direct))
            assert relative < mp.mpf("1e-62")
            product_checks.append({"name": name, "h": h, "k": k, "t": number(t),
                                   "absolute_error": number(error), "scaled_error": number(relative),
                                   "transformation_data": data})

# Exact certificate for the disk |Q| <= 1/20 in the baseline eta example.
r = Fraction(1, 20)
E = (3 * r ** 4 * (2 - r ** 2) / (1 - r ** 2) ** 2
     + 4 * r ** 3 / (1 - r ** 3) ** 2
     + r ** 6 / (1 - r ** 6) ** 2)
T = 3 * r ** 2 + E
assert 0 < T < 1
bound = E / (3 * r ** 2) + T ** 2 / (6 * r ** 2 * (1 - T))
assert 0 < bound < Fraction(1, 2)
# Also provide a simple finite-decimal rational majorant, exactly certified.
decimal_majorant = Fraction(760463, 10 ** 7)
assert bound < decimal_majorant < Fraction(1, 2)
disk_certificate = {
    "radius": rational_text(r), "E": rational_text(E), "T": rational_text(T),
    "H_minus_one_upper_bound": rational_text(bound), "bound_decimal": number(to_mp(bound)),
    "certified_decimal_majorant": rational_text(decimal_majorant),
    "strictly_less_than_one_half": True,
    "exact_one_half_minus_bound": rational_text(Fraction(1, 2) - bound),
    "inverse_s_disk_radius_lower_bound": "1/(20*sqrt(2))",
    "sharper_inverse_s_disk_radius_numeric": number(to_mp(r) * mp.sqrt(1 - to_mp(bound))),
    "proof_note": (
        "For rho=|Q|<=r, put ell=log R. The coefficient majorants give "
        "|ell+3Q^2|<=E(rho), |ell|<=T(rho). Then "
        "|exp(ell)-1-ell|<=T(rho)^2/[2(1-T(rho))]. Divide by 3*rho^2 "
        "and use monotonicity of the resulting nonnegative majorant. "
        "This proves |H(Q)-1|<=bound<1/2 throughout the disk, with H(0)=1. "
        "The analytic square root of H has value 1 at zero. On |Q|=r, "
        "|Q sqrt(H(Q))|>=r sqrt(1-bound)>r/sqrt(2); Rouche's theorem "
        "then gives a unique simple preimage for each |s|<r/sqrt(2)."
    ),
}


def U(t):
    return mp.sqrt(-mp.expm1(-t) / t) * mp.exp(t / 16)


def log_U_derivative(t):
    return 1 / (2 * mp.expm1(t)) - 1 / (2 * t) + mp.mpf(1) / 16


# Exact initial algebraic inverse coefficients: w=1-U(t).
a1 = Fraction(3, 16)
a2 = -Fraction(59, 1536)
a3 = Fraction(41, 8192)
b1 = 1 / a1
b2 = -a2 / a1 ** 3
b3 = 2 * a2 ** 2 / a1 ** 5 - a3 / a1 ** 4
assert a1 * b1 == 1
assert a1 * b2 + a2 * b1 ** 2 == 0
assert a1 * b3 + 2 * a2 * b1 * b2 + a3 * b1 ** 3 == 0
assert b2 / b1 ** 2 == Fraction(59, 288)
raw_qgamma_checks = []
for t in [mp.mpf("0.8"), mp.mpf("1.0"), mp.mpf("1.2"), mp.mpc("1.0", "0.15")]:
    q = mp.exp(-t)
    w = 1 - mp.qgamma(mp.mpf("0.5"), q) / mp.sqrt(mp.pi)
    u = mp.findroot(lambda z: 1 - U(z) - w, t, solver="newton", tol=mp.mpf("1e-70"), verify=True)
    first_correction = 2 * mp.exp(-4 * mp.pi ** 2 / u) / log_U_derivative(u)
    uncorrected_error = abs(u - t)
    corrected_error = abs(u + first_correction - t)
    assert corrected_error < uncorrected_error
    raw_qgamma_checks.append({"original_t": number(t), "endpoint_defect_w": number(w),
                              "algebraic_inverse_u": number(u), "first_flat_correction": number(first_correction),
                              "exact_correction_divided_by_first_sector": number((t - u) / first_correction),
                              "uncorrected_error": number(uncorrected_error),
                              "first_sector_corrected_error": number(corrected_error)})

result = {
    "decimal_precision": mp.mp.dps,
    "cusp_identity": (
        "P(exp(2*pi*i*h/k-t)) = exp(-pi*i*s(h,k))*sqrt(2*pi/(k*t))"
        "*exp(-pi^2/(6*k^2*t)+t/24)"
        "*P(exp(-2*pi*i*h_inverse/k-4*pi^2/(k^2*t)))"
    ),
    "single_factor_cusp_checks": single_checks,
    "general_product_cusp_checks": product_checks,
    "exact_disk_certificate": disk_certificate,
    "raw_half_qgamma_initial_algebraic_inverse_coefficients": [rational_text(x) for x in [b1, b2, b3]],
    "raw_half_qgamma_first_sector": {
        "exact_in_algebraic_inverse_variable": "2*exp(-4*pi^2/u)/(log U)'(u)",
        "leading_as_w_tends_to_zero": "-(32/3)*exp(59*pi^2/72)*exp(-3*pi^2/(4*w))*(1+O(w))",
        "checks": raw_qgamma_checks,
    },
}
(HERE / "cusp_phase_checks.json").write_text(json.dumps(result, indent=2) + "\n")
print("Single-factor cusp identities checked:", len(single_checks))
print("General-product cusp identities checked:", len(product_checks))
print("Exact rational bound on |H-1|:", mp.nstr(to_mp(bound), 24))
print("Certified strict rational majorant:", rational_text(decimal_majorant))
print("Raw half-qGamma algebraic inverse coefficients:", ", ".join(rational_text(x) for x in [b1, b2, b3]))
for check in raw_qgamma_checks:
    print("Raw qGamma t =", check["original_t"], "; corrected inverse error =", check["first_sector_corrected_error"])
