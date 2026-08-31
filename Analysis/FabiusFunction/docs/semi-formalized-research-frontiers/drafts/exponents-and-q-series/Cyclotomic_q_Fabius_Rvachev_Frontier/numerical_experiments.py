#!/usr/bin/env python3
"""Numerical experiments for the cyclotomic q-Fabius/Rvachev report.

The object studied is

    Phi(q,z) = product_{j>=0} sinc((1-q) q^j z),  sinc(z)=sin(z)/z,

for complex |q|<1.  Direct products become ill-conditioned close to a root of
unity because many factors are near a resonant cycle.  Every experiment below
therefore evaluates the absolutely convergent logarithmic series

    log Phi(q,z) = - sum_{k>=1} c_k (1-q)^(2k) z^(2k)/(1-q^(2k)),
    c_k = zeta(2k)/(k*pi^(2k)).

All calculations are deterministic.  High precision is used throughout, and
figures are produced only after the high-precision values have been computed.
The script creates CSV tables, a human-readable summary, and four PDF/PNG
figures in the neighboring data/ and figures/ directories.
"""

from __future__ import annotations

import argparse
import cmath
import csv
import math
from pathlib import Path
from typing import Iterable

import mpmath as mp
import matplotlib.pyplot as plt


HERE = Path(__file__).resolve().parent
DATA_DIR = HERE / "data"
FIG_DIR = HERE / "figures"


def sinc(z: mp.mpc) -> mp.mpc:
    """Entire sinc function with the removable value at zero filled in."""
    return mp.mpf(1) if z == 0 else mp.sin(z) / z


def coeff_c(k: int) -> mp.mpf:
    """Coefficient c_k in log(sinc z) = -sum c_k z^(2k)."""
    return mp.zeta(2 * k) / (k * mp.pi ** (2 * k))


def primitive_root(m: int, h: int = 1) -> mp.mpc:
    """Primitive m-th root exp(2*pi*i*h/m), assuming gcd(h,m)=1."""
    return mp.e ** (2j * mp.pi * h / m)


def resonance_order(m: int) -> int:
    """Order d of omega^2 for a primitive m-th root omega."""
    return m // math.gcd(m, 2)


def log_phi(q: mp.mpc, z: mp.mpc, tol: mp.mpf | None = None,
            max_terms: int = 10000) -> mp.mpc:
    """Evaluate the analytic logarithm of Phi(q,z) from its power series.

    This branch is normalized by log Phi(q,0)=0.  The series is used only in
    the disk |(1-q)z|<pi, where it converges absolutely and uniformly on
    compact subsets.  A relative-plus-absolute tail test is applied after a
    few terms; the geometric decay in all experiments is very rapid.
    """
    if abs(q) >= 1:
        raise ValueError("log_phi requires |q|<1")
    if abs((1 - q) * z) >= mp.pi:
        raise ValueError("series evaluation requires |(1-q)z|<pi")
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 20))

    total = mp.mpc(0)
    small_count = 0
    for k in range(1, max_terms + 1):
        denominator = 1 - q ** (2 * k)
        term = -coeff_c(k) * ((1 - q) * z) ** (2 * k) / denominator
        total += term
        threshold = tol * max(mp.mpf(1), abs(total))
        if abs(term) < threshold:
            small_count += 1
            if small_count >= 6:
                return total
        else:
            small_count = 0
    raise RuntimeError("log_phi did not meet the requested tolerance")


def action_series(omega: mp.mpc, d: int, z: mp.mpc,
                  tol: mp.mpf | None = None) -> mp.mpc:
    """Root-of-unity action A_omega(z) from the resonant coefficient series."""
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 20))
    total = mp.mpc(0)
    small_count = 0
    for ell in range(1, 10000):
        k = ell * d
        term = coeff_c(k) * (1 - omega) ** (2 * k) * z ** (2 * k) / (2 * k)
        total += term
        if abs(term) < tol * max(mp.mpf(1), abs(total)):
            small_count += 1
            if small_count >= 5:
                return total
        else:
            small_count = 0
    raise RuntimeError("action series did not converge")


def boundary_constant_B(omega: mp.mpc, d: int, z: mp.mpc,
                        tol: mp.mpf | None = None) -> mp.mpc:
    """Constant B_omega(z) in log Phi = -A/delta + B + O(delta)."""
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 20))
    total = mp.mpc(0)
    small_count = 0
    for k in range(1, 10000):
        a2k = (1 - omega) ** (2 * k)
        if k % d:
            term = -coeff_c(k) * a2k * z ** (2 * k) / (1 - omega ** (2 * k))
        else:
            constant_ratio = omega / (1 - omega) + mp.mpf(2 * k - 1) / (4 * k)
            term = -coeff_c(k) * a2k * constant_ratio * z ** (2 * k)
        total += term
        if abs(term) < tol * max(mp.mpf(1), abs(total)):
            small_count += 1
            if small_count >= 6:
                return total
        else:
            small_count = 0
    raise RuntimeError("boundary constant series did not converge")


def leading_A(omega: mp.mpc, d: int) -> mp.mpc:
    """Leading cyclotomic constant A_omega."""
    return coeff_c(d) * (1 - omega) ** (2 * d) / (2 * d)


def subcritical_C(omega: mp.mpc, k: int) -> mp.mpc:
    """Coefficient C_{k,omega} for 1<=k<d."""
    return coeff_c(k) * (1 - omega) ** (2 * k) / (1 - omega ** (2 * k))


def eta_constant(omega: mp.mpc, d: int) -> mp.mpc:
    return 2 * d * omega / (1 - omega) + mp.mpf(2 * d - 1) / 2


def D_constant(omega: mp.mpc, d: int) -> mp.mpc:
    return coeff_c(2 * d) * (1 - omega) ** (4 * d) / (4 * d)


def complex_string(z: mp.mpc, digits: int = 18) -> str:
    """Stable compact representation for CSV/text output."""
    re = mp.nstr(mp.re(z), digits)
    im = mp.nstr(abs(mp.im(z)), digits)
    sign = "+" if mp.im(z) >= 0 else "-"
    return f"{re}{sign}{im}j"


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def radial_action_experiment() -> list[dict[str, object]]:
    """Check the fixed-frequency two-term root-of-unity expansion."""
    z = mp.mpf("0.8")  # safely inside the uniform natural-boundary interval
    deltas = [mp.mpf(x) for x in ("0.12", "0.08", "0.05", "0.03", "0.02",
                                      "0.012", "0.008", "0.005", "0.003")]
    rows: list[dict[str, object]] = []

    plt.figure(figsize=(7.2, 4.8))
    for m in (2, 3, 4, 6):
        omega = primitive_root(m)
        d = resonance_order(m)
        action = action_series(omega, d, z)
        const_b = boundary_constant_B(omega, d, z)
        x_values: list[float] = []
        errors: list[float] = []
        for delta in deltas:
            q = omega * (1 - delta)
            value = log_phi(q, z)
            action_error = abs(delta * value + action)
            corrected_error = abs(value + action / delta - const_b)
            rows.append({
                "m": m,
                "d": d,
                "delta": mp.nstr(delta, 16),
                "action": complex_string(action),
                "B": complex_string(const_b),
                "log_phi": complex_string(value),
                "abs_delta_log_plus_A": mp.nstr(action_error, 18),
                "abs_two_term_residual": mp.nstr(corrected_error, 18),
            })
            x_values.append(float(delta))
            errors.append(float(corrected_error))
        plt.loglog(x_values, errors, marker="o", label=f"m={m}, d={d}")

    reference_x = [float(d) for d in deltas]
    scale = max(float(r["abs_two_term_residual"]) for r in rows if r["m"] == 2) / max(reference_x)
    plt.loglog(reference_x, [scale * x for x in reference_x], linestyle="--", label="slope 1")
    plt.xlabel(r"radial distance $\delta$")
    plt.ylabel(r"$|\log\Phi+\mathcal{A}/\delta-\mathcal{B}|$")
    plt.title("Two-term radial root-of-unity expansion")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG_DIR / "radial_action_convergence.pdf")
    plt.savefig(FIG_DIR / "radial_action_convergence.png", dpi=180)
    plt.close()
    return rows


def blowup_experiment() -> list[dict[str, object]]:
    """Test the polyharmonic limit and its first two correction layers."""
    w = mp.mpf("1.2")
    epsilons = [mp.mpf(x) for x in ("0.24", "0.18", "0.13", "0.09", "0.065",
                                        "0.045", "0.032", "0.023", "0.016")]
    rows: list[dict[str, object]] = []

    plt.figure(figsize=(7.2, 4.8))
    for m in (3, 4, 6):
        omega = primitive_root(m)
        d = resonance_order(m)
        a_const = leading_A(omega, d)
        eta = eta_constant(omega, d)
        d_const = D_constant(omega, d)
        xs: list[float] = []
        full_errors: list[float] = []
        for eps in epsilons:
            q = omega * (1 - eps ** d)
            z = mp.sqrt(eps) * w
            value = log_phi(q, z)
            limit_log = -a_const * w ** (2 * d)
            subcritical = mp.mpc(0)
            for k in range(1, d):
                subcritical += subcritical_C(omega, k) * eps ** k * w ** (2 * k)
            order_d = eps ** d * (a_const * eta * w ** (2 * d)
                                  + d_const * w ** (4 * d))
            raw_error = abs(value - limit_log)
            subcritical_error = abs(value - limit_log + subcritical)
            full_error = abs(value - limit_log + subcritical + order_d)
            rows.append({
                "m": m,
                "d": d,
                "epsilon": mp.nstr(eps, 16),
                "A": complex_string(a_const),
                "log_phi": complex_string(value),
                "raw_error": mp.nstr(raw_error, 18),
                "after_subcritical_error": mp.nstr(subcritical_error, 18),
                "after_order_d_error": mp.nstr(full_error, 18),
            })
            xs.append(float(eps))
            full_errors.append(float(full_error))
        plt.loglog(xs, full_errors, marker="o", label=f"m={m}: predicted slope {d+1}")

    # Reference slopes are normalized to the last point of each corresponding series.
    for m in (3, 4, 6):
        d = resonance_order(m)
        subset = [r for r in rows if r["m"] == m]
        xs = [float(r["epsilon"]) for r in subset]
        ys = [float(r["after_order_d_error"]) for r in subset]
        scale = ys[-1] / (xs[-1] ** (d + 1))
        plt.loglog(xs, [scale * x ** (d + 1) for x in xs], linestyle="--", alpha=0.55)
    plt.xlabel(r"blow-up parameter $\epsilon$")
    plt.ylabel("absolute log-error after all displayed corrections")
    plt.title("Cyclotomic blow-up: all displayed terms removed")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG_DIR / "cyclotomic_blowup_errors.pdf")
    plt.savefig(FIG_DIR / "cyclotomic_blowup_errors.png", dpi=180)
    plt.close()
    return rows


def cumulants(q: mp.mpc, n_max: int) -> list[mp.mpc]:
    """Cumulants of the formal q-uniform law Y_q through order n_max."""
    kappas = [mp.mpc(0) for _ in range(n_max + 1)]
    for k in range(1, n_max // 2 + 1):
        order = 2 * k
        prefactor = mp.mpf(2) ** (2 * k - 1) * mp.bernpoly(2 * k, 0) / k
        # mp.bernpoly(n,0) is the Bernoulli number B_n.
        kappas[order] = prefactor * (1 - q) ** order / (1 - q ** order)
    return kappas


def moments_from_cumulants(kappas: list[mp.mpc]) -> list[mp.mpc]:
    """Complete Bell recurrence m_n=sum binom(n-1,j-1) kappa_j m_{n-j}."""
    n_max = len(kappas) - 1
    moments = [mp.mpc(0) for _ in range(n_max + 1)]
    moments[0] = mp.mpf(1)
    for n in range(1, n_max + 1):
        value = mp.mpc(0)
        for j in range(1, n + 1):
            value += math.comb(n - 1, j - 1) * kappas[j] * moments[n - j]
        moments[n] = value
    return moments


def bell_collapse_experiment() -> list[dict[str, object]]:
    """Verify that only the 2d-th scaled cumulant survives."""
    epsilons = [mp.mpf(x) for x in ("0.24", "0.18", "0.13", "0.09", "0.065",
                                        "0.045", "0.032", "0.023", "0.016")]
    rows: list[dict[str, object]] = []

    plt.figure(figsize=(7.2, 4.8))
    for m in (4, 6):
        omega = primitive_root(m)
        d = resonance_order(m)
        a_const = leading_A(omega, d)
        b_const = (-1) ** (d + 1) * a_const
        tracked_order = 2 * d
        xs: list[float] = []
        errs: list[float] = []
        for eps in epsilons:
            q = omega * (1 - eps ** d)
            n_max = 4 * d
            kappa = cumulants(q, n_max)
            moments = moments_from_cumulants(kappa)
            for n in range(2, n_max + 1, 2):
                scaled_kappa = eps ** (n // 2) * kappa[n]
                if n == 2 * d:
                    kappa_limit = math.factorial(2 * d) * b_const
                else:
                    kappa_limit = mp.mpc(0)
                scaled_moment = eps ** (mp.mpf(n) / 2) * moments[n]
                if n % (2 * d) == 0:
                    r = n // (2 * d)
                    moment_limit = mp.factorial(n) * b_const ** r / mp.factorial(r)
                else:
                    moment_limit = mp.mpc(0)
                rows.append({
                    "m": m,
                    "d": d,
                    "epsilon": mp.nstr(eps, 16),
                    "order": n,
                    "scaled_cumulant": complex_string(scaled_kappa),
                    "cumulant_limit": complex_string(kappa_limit),
                    "scaled_moment": complex_string(scaled_moment),
                    "moment_limit": complex_string(moment_limit),
                    "moment_abs_error": mp.nstr(abs(scaled_moment - moment_limit), 18),
                })
            scaled_kappa = eps ** d * kappa[tracked_order]
            kappa_limit = math.factorial(tracked_order) * b_const
            xs.append(float(eps))
            errs.append(float(abs(scaled_kappa - kappa_limit)))
        plt.loglog(xs, errs, marker="o", label=f"m={m}, surviving order {2*d}")

    plt.xlabel(r"$\epsilon$")
    plt.ylabel("error in the surviving scaled cumulant")
    plt.title("Bell-cumulant condensation at cyclotomic scale")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG_DIR / "bell_moment_collapse.pdf")
    plt.savefig(FIG_DIR / "bell_moment_collapse.png", dpi=180)
    plt.close()
    return rows


def inverse_w_experiment() -> list[dict[str, object]]:
    """Track an inverse frequency branch near the fourth root of unity."""
    m = 4
    omega = primitive_root(m)
    d = resonance_order(m)
    target = mp.mpf("1.1")
    ell = mp.log(target)
    a_const = leading_A(omega, d)
    c1 = subcritical_C(omega, 1)
    # Select the positive-real fourth root of -ell/A.
    w0 = mp.root(-ell / a_const, 2 * d)
    w1 = -c1 * w0 ** (3 - 2 * d) / (2 * d * a_const)
    epsilons = [mp.mpf(x) for x in ("0.07", "0.05", "0.035", "0.025", "0.018",
                                        "0.013", "0.009", "0.0065")]
    rows: list[dict[str, object]] = []
    xs: list[float] = []
    errs: list[float] = []
    previous = w0
    for eps in epsilons:
        q = omega * (1 - eps ** d)

        def equation(w: mp.mpc) -> mp.mpc:
            return log_phi(q, mp.sqrt(eps) * w) - ell

        seed = w0 + w1 * eps
        # One complex variable is represented directly by mpmath's complex secant method.
        exact = mp.findroot(equation, (seed, seed * (1 + mp.mpf("1e-5")) + mp.mpf("1e-7")))
        first_order = w0 + w1 * eps
        error = abs(exact - first_order)
        rows.append({
            "epsilon": mp.nstr(eps, 16),
            "target": mp.nstr(target, 16),
            "w0": complex_string(w0),
            "w1": complex_string(w1),
            "w_exact": complex_string(exact),
            "w_first_order": complex_string(first_order),
            "abs_error": mp.nstr(error, 18),
        })
        previous = exact
        xs.append(float(eps))
        errs.append(float(error))

    plt.figure(figsize=(7.2, 4.8))
    plt.loglog(xs, errs, marker="o", label="computed inverse branch")
    scale = errs[-1] / xs[-1] ** 2
    plt.loglog(xs, [scale * x ** 2 for x in xs], linestyle="--", label="slope 2")
    plt.xlabel(r"$\epsilon$")
    plt.ylabel(r"$|w(\epsilon)-w_0-w_1\epsilon|$")
    plt.title("Inverse cyclotomic frequency branch, m=4")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG_DIR / "inverse_branch_errors.pdf")
    plt.savefig(FIG_DIR / "inverse_branch_errors.png", dpi=180)
    plt.close()
    return rows


def inverse_q_experiment() -> list[dict[str, object]]:
    """Check the small-z branch q(z) approaching omega=i for fixed Phi=y."""
    m = 4
    omega = primitive_root(m)
    d = resonance_order(m)
    target = mp.mpf("1.1")
    ell = mp.log(target)
    a_const = leading_A(omega, d)
    c1 = subcritical_C(omega, 1)
    z_values = [mp.mpf(x) for x in ("0.42", "0.36", "0.31", "0.27", "0.23",
                                       "0.20", "0.17", "0.145")]
    rows: list[dict[str, object]] = []
    for z in z_values:
        leading_delta = -a_const * z ** (2 * d) / ell
        second_delta = leading_delta * (1 - c1 * z ** 2 / ell)

        def equation(delta: mp.mpc) -> mp.mpc:
            q = omega * (1 - delta)
            return log_phi(q, z) - ell

        exact_delta = mp.findroot(
            equation,
            (second_delta, second_delta * (1 + mp.mpf("1e-5")) + mp.mpf("1e-12")),
        )
        rows.append({
            "z": mp.nstr(z, 16),
            "target": mp.nstr(target, 16),
            "delta_exact": complex_string(exact_delta),
            "delta_leading": complex_string(leading_delta),
            "delta_two_term": complex_string(second_delta),
            "leading_error": mp.nstr(abs(exact_delta - leading_delta), 18),
            "two_term_error": mp.nstr(abs(exact_delta - second_delta), 18),
            "q_exact": complex_string(omega * (1 - exact_delta)),
        })
    return rows


def create_summary(radial_rows: list[dict[str, object]],
                   blowup_rows: list[dict[str, object]],
                   bell_rows: list[dict[str, object]],
                   inverse_rows: list[dict[str, object]],
                   inverse_q_rows: list[dict[str, object]]) -> None:
    """Write a concise diagnostics file consumed by the LaTeX report."""
    lines: list[str] = []
    lines.append("Cyclotomic q-Fabius/Rvachev numerical diagnostics")
    lines.append(f"mpmath decimal precision: {mp.mp.dps}")
    lines.append("")

    lines.append("Leading cyclotomic constants A_omega:")
    for m in (2, 3, 4, 5, 6, 8, 10):
        omega = primitive_root(m)
        d = resonance_order(m)
        lines.append(f"  m={m:2d}, d={d:2d}, A={complex_string(leading_A(omega,d), 30)}")
    lines.append("")

    lines.append("Smallest two-term radial residual in each tested root order:")
    for m in (2, 3, 4, 6):
        subset = [r for r in radial_rows if r["m"] == m]
        best = subset[-1]
        lines.append(
            f"  m={m}: delta={best['delta']}, residual={best['abs_two_term_residual']}"
        )
    lines.append("")

    lines.append("Smallest fully corrected cyclotomic log-error:")
    for m in (3, 4, 6):
        subset = [r for r in blowup_rows if r["m"] == m]
        best = subset[-1]
        lines.append(
            f"  m={m}: epsilon={best['epsilon']}, error={best['after_order_d_error']}"
        )
    lines.append("")

    lines.append("Inverse frequency branch (m=4) last point:")
    last = inverse_rows[-1]
    lines.append(
        f"  epsilon={last['epsilon']}, exact={last['w_exact']}, first-order error={last['abs_error']}"
    )
    lines.append("")

    lines.append("Inverse q-branch (m=4) last point:")
    lastq = inverse_q_rows[-1]
    lines.append(
        f"  z={lastq['z']}, exact delta={lastq['delta_exact']}, two-term error={lastq['two_term_error']}"
    )
    lines.append("")

    # Record one representative Bell-collapse row for each model.
    lines.append("Representative scaled moment checks:")
    for m in (4, 6):
        d = resonance_order(m)
        candidates = [r for r in bell_rows if r["m"] == m and r["order"] == 2*d]
        row = candidates[-1]
        lines.append(
            f"  m={m}, order={2*d}, epsilon={row['epsilon']}, "
            f"moment={row['scaled_moment']}, limit={row['moment_limit']}"
        )

    (DATA_DIR / "experiment_summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=80, help="mpmath decimal precision")
    args = parser.parse_args()
    mp.mp.dps = args.dps
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    FIG_DIR.mkdir(parents=True, exist_ok=True)

    radial = radial_action_experiment()
    write_csv(
        DATA_DIR / "radial_action.csv",
        ["m", "d", "delta", "action", "B", "log_phi",
         "abs_delta_log_plus_A", "abs_two_term_residual"],
        radial,
    )

    blowup = blowup_experiment()
    write_csv(
        DATA_DIR / "cyclotomic_blowup.csv",
        ["m", "d", "epsilon", "A", "log_phi", "raw_error",
         "after_subcritical_error", "after_order_d_error"],
        blowup,
    )

    bell = bell_collapse_experiment()
    write_csv(
        DATA_DIR / "bell_moment_collapse.csv",
        ["m", "d", "epsilon", "order", "scaled_cumulant", "cumulant_limit",
         "scaled_moment", "moment_limit", "moment_abs_error"],
        bell,
    )

    inverse = inverse_w_experiment()
    write_csv(
        DATA_DIR / "inverse_frequency_branch.csv",
        ["epsilon", "target", "w0", "w1", "w_exact", "w_first_order", "abs_error"],
        inverse,
    )

    inverse_q = inverse_q_experiment()
    write_csv(
        DATA_DIR / "inverse_q_branch.csv",
        ["z", "target", "delta_exact", "delta_leading", "delta_two_term",
         "leading_error", "two_term_error", "q_exact"],
        inverse_q,
    )

    create_summary(radial, blowup, bell, inverse, inverse_q)
    print((DATA_DIR / "experiment_summary.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
