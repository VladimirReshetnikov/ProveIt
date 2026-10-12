"""Independent high precision diagnostics for the critical order-three crossover.

Run with Python and mpmath. Roots use the original polylogarithm defect;
the analytic chart is checked separately via its paired equation.
These are numerical diagnostics, not interval certificates.
"""
import json
import argparse
from pathlib import Path
import mpmath as mp

mp.mp.dps = 200
A0 = mp.zeta(2)
A1 = mp.diff(mp.zeta, 2)
A2 = mp.diff(mp.zeta, 2, 2)
gamma1 = mp.stieltjes(1)


def scalar(x, digits=32):
    return mp.nstr(x, digits)


def run_one(lam, X):
    lam, X = mp.mpf(lam), mp.mpf(X)
    h, q = 1 / X, 1 / mp.sqrt(X)
    z, delta = mp.exp(-X), mp.exp(-2 * X)
    eps = lam / X
    order = 3 + eps
    A = mp.zeta(2 + eps)
    C = -mp.expm1(-lam) / lam if lam else mp.mpf(1)
    E = mp.exp(-lam)
    U0 = mp.sqrt(2 * A0 / C)
    leading = z * q * U0

    def original_delta(x):
        deficit = mp.zeta(order) - mp.polylog(order, mp.exp(-x))
        return x + A - mp.sqrt(A * A + 2 * deficit)

    ratio = mp.findroot(
        lambda v: original_delta(leading * v) / delta - 1,
        (mp.mpf("0.75"), mp.mpf("1.25")),
        tol=mp.mpf("1e-130"), maxsteps=100,
    )
    exact = leading * ratio

    E2 = mp.gamma(1 - eps) / ((1 + eps) * (1 + eps / 2))

    def H(x):
        if not eps:
            return -mp.log(x) + mp.mpf("2.5")
        return 1 + mp.zeta(1 + eps) - E2 * mp.exp(eps * mp.log(x)) / eps

    def tail(x):
        return 2 * mp.fsum(
            (-1) ** k * mp.zeta(3 + eps - k) * x ** (k - 3)
            / mp.factorial(k) for k in range(3, 45)
        )

    paired_residual = (
        exact ** 2 * (H(exact) + exact * tail(exact))
        - delta * (2 * A + 2 * exact - delta)
    ) / (2 * A * delta)

    D = mp.log(X) / 2 - mp.log(U0) - mp.euler + mp.mpf("1.5")
    B = E * D + 1 + mp.euler
    d1 = lam * A1 / (2 * A0) - B / (2 * C)
    kappa2 = A0 + mp.mpf(5) / 4
    b1 = -E * d1 - lam * (gamma1 + E * (kappa2 + D * D) / 2)
    d2 = lam * lam * A2 / (4 * A0) - d1 * d1 / 2 - d1 * B / C - b1 / (2 * C)
    first = leading * (1 + d1 / X)
    second = leading * (1 + d1 / X + d2 / (X * X))

    U_alg = mp.findroot(
        lambda U: U * U * h * H(z * q * U) - 2 * A,
        (U0 * mp.mpf("0.75"), U0 * mp.mpf("1.25")),
        tol=mp.mpf("1e-160"), maxsteps=100,
    )
    algebraic = z * q * U_alg
    G = h * H(algebraic)
    M = E2 * mp.exp(eps * mp.log(algebraic))
    first_exponential = delta * h * (
        2 + h * U_alg * U_alg * mp.zeta(eps) / 3
    ) / (2 * G - h * M)
    exp_ratio = (exact - algebraic) / first_exponential

    err1 = first / exact - 1
    err2 = second / exact - 1
    return {
        "lambda": scalar(lam), "X": scalar(X), "order": scalar(order),
        "exact_x": scalar(exact, 65),
        "original_relative_residual": scalar(original_delta(exact) / delta - 1),
        "paired_relative_residual": scalar(paired_residual),
        "leading_relative_error": scalar(leading / exact - 1),
        "first_relative_error": scalar(err1),
        "first_scaled_error": scalar(err1 * X ** 2 / (1 + mp.log(X)) ** 2),
        "second_relative_error": scalar(err2),
        "second_scaled_error": scalar(err2 * X ** 3 / (1 + mp.log(X)) ** 3),
        "first_exponential_correction": scalar(first_exponential, 50),
        "exponential_correction_ratio_minus_one": scalar(exp_ratio - 1),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent.parent / "data")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows = []
    for lam in (-2, 0, 2):
        for X in (20, 40, 80):
            row = run_one(lam, X)
            rows.append(row)
            print(json.dumps(row), flush=True)
    output = {
        "precision_decimal_digits": mp.mp.dps,
        "status": "numerical diagnostics, not interval-certified",
        "rows": rows,
    }
    (args.output_dir / "crossover_checks.json").write_text(
        json.dumps(output, indent=2) + "\n"
    )
