#!/usr/bin/env python3
"""Independent numerical diagnostics for the complex cotangent-power theorem.

Run with Python 3 and mpmath.  These comparisons are diagnostics, not proofs.
The theorem is proved by Fourier expansion and local Mellin subtractions.
"""
from __future__ import annotations

import json
from pathlib import Path
import platform
import time

import mpmath as mp

mp.mp.dps = 65
OUT = Path(__file__).with_name("complex_powers_verification.json")


def rep(z):
    return {"real": mp.nstr(mp.re(z), 55), "imag": mp.nstr(mp.im(z), 55)}


def row(name, actual, expected, **extra):
    err = abs(actual - expected)
    return {
        "name": name,
        "actual": rep(actual),
        "expected": rep(expected),
        "absolute_residual": mp.nstr(err, 8),
        "scaled_residual": mp.nstr(err / max(1, abs(expected)), 8),
        **extra,
    }


def coords(z):
    eps = 1 if mp.im(z) > 0 else -1
    a = z + eps * mp.pi * 1j
    return -1 / a, (z - eps * mp.pi * 1j) / a, -eps * 2j * mp.pi


def log_mellin_ratio(t, q):
    v = mp.exp(-t)
    return mp.log(-mp.expm1(-t)) - mp.log1p(-q * v)


def binomial_polylog_mellin(lam, u, q):
    fun = lambda t: t ** (u - 1) * mp.expm1(lam * log_mellin_ratio(t, q))
    return mp.quad(fun, [0, mp.mpf(".2"), 1, 4, 12, 40, mp.inf]) / mp.gamma(u)


def resolvent_power(x, z, lam):
    if x == 0 or x == 1:
        return mp.mpc(0)
    val = 1 / (mp.pi * mp.cot(mp.pi * x) - z)
    return mp.exp(lam * mp.log(val))


def falling_spectral(s, p):
    ans = mp.mpc(1)
    for j in range(1, p + 1):
        ans *= s - j
    return ans


def master_direct(s, lam, z, p):
    pref = falling_spectral(s, p)
    def integrand(x):
        if x == 0 or x == 1:
            return mp.mpc(0)
        return pref * mp.zeta(1 + p - s, x) * resolvent_power(x, z, lam)
    return mp.quad(integrand, [0, mp.mpf(".1"), mp.mpf(".4"), mp.mpf(".75"), 1])


def master_mellin(s, lam, z, p):
    A, q, sigma = coords(z)
    return (mp.exp(lam * mp.log(A)) * mp.gamma(s)
            * mp.exp((p - s) * mp.log(sigma))
            * binomial_polylog_mellin(lam, s - p, q))


def complete_harmonic(lam, n):
    """Coefficient of exp(sum_{r>=1} H_lam^(r) t^r/r)."""
    harm = [mp.mpc(0), mp.digamma(1 + lam) + mp.euler]
    harm.extend(mp.zeta(r) - mp.zeta(r, 1 + lam) for r in range(2, n + 1))
    ans = [mp.mpc(1)]
    for k in range(1, n + 1):
        ans.append(sum(harm[r] * ans[k - r] for r in range(1, k + 1)) / k)
    return ans[n]


def first_jet_mellin(u, q):
    fun = lambda t: t ** (u - 1) * log_mellin_ratio(t, q)
    return mp.quad(fun, [0, mp.mpf(".2"), 1, 4, 12, 40, mp.inf]) / mp.gamma(u)


def special_D(lam, n):
    """Coefficients of (R_(i*pi)(x)/x)^lam from its sine product."""
    ell = [mp.mpc(0)] * (n + 1)
    if n >= 1:
        ell[1] = mp.pi * 1j
    for k in range(1, n // 2 + 1):
        ell[2 * k] = -mp.zeta(2 * k) / k
    d = [mp.mpc(1)]
    for j in range(1, n + 1):
        d.append(lam * sum(k * ell[k] * d[j - k] for k in range(1, j + 1)) / j)
    return d


def local_gamma_second(lam, n=70):
    """Coefficients of gamma_0''(x) R_(i*pi)(x)^lam / x^(lam-3)."""
    d = special_D(lam, n)
    reg = [(-1) ** k * (k + 1) * (k + 2) * mp.zeta(k + 3) for k in range(n)]
    coeff = []
    for j in range(n + 1):
        cj = 2 * d[j]
        if j >= 3:
            cj += sum(d[k] * reg[j - 3 - k] for k in range(j - 2))
        coeff.append(cj)
    return coeff


def continued_gamma_second(lam, finite_part_at_one=False):
    """Continuation by independent local x-Taylor subtraction, not L_lambda."""
    delta = mp.mpf(".05")
    coeff = local_gamma_second(lam)
    local = mp.mpc(0)
    for j, cj in enumerate(coeff):
        denom = lam + j - 2
        if finite_part_at_one and j == 1:
            local += cj * mp.log(delta)
        else:
            local += cj * delta ** denom / denom
    def fun(x):
        if x == 1:
            return mp.mpc(0)
        r = mp.exp(mp.pi * 1j * x) * mp.sin(mp.pi * x) / mp.pi
        return -mp.polygamma(2, x) * mp.exp(lam * mp.log(r))
    return local + mp.quad(fun, [delta, mp.mpf(".25"), mp.mpf(".55"), mp.mpf(".8"), 1])


def laurent_ct_by_richardson():
    # Symmetric samples cancel the simple pole and all odd analytic powers.
    hs = [mp.mpf(".01") / (2 ** k) for k in range(8)]
    samples = [
        (continued_gamma_second(1 + h) + continued_gamma_second(1 - h)) / 2
        for h in hs
    ]
    work = list(samples)
    for order in range(1, len(work)):
        scale = mp.mpf(4) ** order
        work = [(scale * work[j + 1] - work[j]) / (scale - 1)
                for j in range(len(work) - 1)]
    return work[0], [{"h": mp.nstr(h, 12), "symmetric_value": rep(v)}
                    for h, v in zip(hs, samples)]


def main():
    start = time.time()
    data = {
        "method": "Numerical diagnostics; no residual is used as a mathematical proof.",
        "python": platform.python_version(),
        "mpmath": mp.__version__,
        "decimal_precision": mp.mp.dps,
        "checks": [],
    }
    checks = data["checks"]
    cases = [
        (mp.mpc("2.6", ".15"), mp.mpc(".4", ".3"), 1j * mp.pi, 0),
        (mp.mpc("3.4", ".25"), mp.mpc(".8", "-.2"), mp.mpc(".7", "2.3"), 1),
        (mp.mpc("4.2", "-.3"), mp.mpc("1.2", ".1"), mp.mpc("-.4", "-3.9"), 2),
    ]
    for j, (s, lam, z, p) in enumerate(cases, 1):
        checks.append(row(f"joint_generator_{j}", master_direct(s, lam, z, p),
                          master_mellin(s, lam, z, p),
                          s=rep(s), lam=rep(lam), z=rep(z), p=p))
    for lam in [mp.mpc(".4", ".3"), mp.mpc("2.2", "-.3")]:
        for n in [1, 2, 3, 5]:
            checks.append(row(f"gamma_closure_n{n}",
                              binomial_polylog_mellin(lam, n, 0),
                              -complete_harmonic(lam, n), lam=rep(lam)))
    for u, q in [(mp.mpc("1.7", ".2"), mp.mpc(".3", ".2")),
                 (mp.mpf("2.3"), mp.mpf("-.4"))]:
        checks.append(row("first_exponent_jet", first_jet_mellin(u, q),
                          mp.polylog(u + 1, q) - mp.zeta(u + 1),
                          u=rep(u), q=rep(q)))

    L = mp.log(2 * mp.pi) - mp.pi * 1j / 2
    expected_fp = 2j * mp.pi * (mp.mpf("1.5") - mp.euler - L)
    expected_ct = 2j * mp.pi * (mp.mpf("2.5") - mp.euler - L)
    observed_fp = continued_gamma_second(mp.mpf(1), finite_part_at_one=True)
    observed_ct, samples = laurent_ct_by_richardson()
    checks.append(row("fixed_exponent_x_finite_part", observed_fp, expected_fp))
    checks.append(row("exponent_laurent_constant", observed_ct, expected_ct))
    checks.append(row("noncommutation_correction", observed_ct - observed_fp, 2j * mp.pi))
    data["laurent_extrapolation_samples"] = samples
    data["maximum_scaled_residual"] = mp.nstr(max(mp.mpf(r["scaled_residual"]) for r in checks), 8)
    data["elapsed_seconds"] = round(time.time() - start, 3)
    data["all_scaled_residuals_below_1e_28"] = all(
        mp.mpf(r["scaled_residual"]) < mp.mpf("1e-28") for r in checks
    )
    OUT.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({
        "checks": len(checks),
        "maximum_scaled_residual": data["maximum_scaled_residual"],
        "all_scaled_residuals_below_1e_28": data["all_scaled_residuals_below_1e_28"],
        "elapsed_seconds": data["elapsed_seconds"],
        "output": str(OUT),
    }, indent=2))


if __name__ == "__main__":
    main()
