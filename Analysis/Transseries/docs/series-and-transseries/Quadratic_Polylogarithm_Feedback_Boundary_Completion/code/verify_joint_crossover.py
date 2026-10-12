"""High precision diagnostics for joint feedback/order crossover and a local fold.

Real roots are computed from the original polylogarithm deficit equation.
The paired convergent series is an independent residual check. The optional
complex fold is located with the paired equation and checked in the original
equation; no global inverse-sheet identification is asserted there.

Example: python verify_joint_crossover.py --output-dir results --X 40 80
These numerical calculations are diagnostics, not interval certificates.
"""
import argparse
import json
from pathlib import Path

import mpmath as mp


def fmt(value, digits=36):
    return mp.nstr(value, digits)


def complex_record(value, digits=50):
    return {"real": fmt(mp.re(value), digits), "imag": fmt(mp.im(value), digits)}


def E2(eps):
    return mp.gamma(1 - eps) / ((1 + eps) * (1 + eps / 2))


def tail(eps, x, derivative=0):
    total = mp.mpf(0)
    for k in range(3 + derivative, 45):
        power = k - 3
        falling = mp.factorial(power) / mp.factorial(power - derivative)
        total += (2 * (-1) ** k * mp.zeta(3 + eps - k)
                  * falling * x ** (power - derivative) / mp.factorial(k))
    return total


def real_case(lam, eta, X):
    lam, eta, X = mp.mpf(lam), mp.mpf(eta), mp.mpf(X)
    z, d = mp.exp(-X), mp.exp(-2 * X)
    q, j = 1 / mp.sqrt(X), z * mp.sqrt(X)
    eps, order = lam / X, 3 + lam / X
    A, A0 = mp.zeta(2 + eps), mp.zeta(2)
    b = A + eta * j
    C = -mp.expm1(-lam) / lam if lam else mp.mpf(1)
    S = mp.sqrt(eta * eta + 2 * A0 * C)
    V0 = 2 * A0 / (S + eta)
    leading = z * q * V0
    zeta_order = mp.zeta(order)

    def original(x):
        deficit = zeta_order - mp.polylog(order, mp.exp(-x))
        square_root = mp.sqrt(b * b + 2 * deficit)
        return x + b - square_root, square_root

    def psi_prime(x):
        _, square_root = original(x)
        return 1 - mp.polylog(order - 1, mp.exp(-x)) / square_root

    ratio = mp.findroot(
        lambda v: original(leading * v)[0] / d - 1,
        (mp.mpf("0.7"), mp.mpf("1.3")),
        tol=mp.mpf("1e-110"), maxsteps=100,
    )
    exact = leading * ratio
    original_residual = original(exact)[0] / d - 1
    if eps:
        H = 1 + mp.zeta(1 + eps) - E2(eps) * mp.exp(eps * mp.log(exact)) / eps
    else:
        H = -mp.log(exact) + mp.mpf("2.5")
    paired_residual = (
        2 * (b - A) * exact
        + exact * exact * (H + exact * tail(eps, exact))
        - d * (2 * b + 2 * exact - d)
    ) / (2 * A * d)

    B = (mp.exp(-lam) * (mp.log(X) / 2 - mp.log(V0)
                         - mp.euler + mp.mpf("1.5")) + 1 + mp.euler)
    V1 = (2 * lam * mp.diff(mp.zeta, 2) - V0 * V0 * B) / (2 * S)
    first = z * q * (V0 + V1 / X)
    first_error = first / exact - 1
    derivative_at_root = psi_prime(exact)
    record = {
        "lambda": fmt(lam), "eta": fmt(eta), "X": fmt(X),
        "order": fmt(order), "b_minus_A": fmt(b - A),
        "exact_x": fmt(exact, 70),
        "original_relative_residual": fmt(original_residual),
        "paired_relative_residual": fmt(paired_residual),
        "leading_relative_error": fmt(leading / exact - 1),
        "first_relative_error": fmt(first_error),
        "first_scaled_error": fmt(first_error * X * X / (1 + mp.log(X)) ** 2),
        "psi_prime_at_zero": fmt(1 - A / b),
        "psi_prime_at_root": fmt(derivative_at_root),
        "positive_root": bool(exact > 0),
        "positive_derivative_at_root": bool(derivative_at_root > 0),
    }
    if eta < 0:
        # Psi has a negative minimum. The root for d>0 must lie beyond it in x,
        # equivalently before the interior fold when followed from t=0.
        fold_scale = z * q * (-eta / C)
        fold_ratio = mp.findroot(
            lambda v: psi_prime(fold_scale * v) / j,
            (mp.mpf("0.7"), mp.mpf("1.3")),
            tol=mp.mpf("1e-110"), maxsteps=100,
        )
        fold_x = fold_scale * fold_ratio
        fold_d = original(fold_x)[0]
        record["interior_fold"] = {
            "x_fold": fmt(fold_x, 60),
            "d_fold": fmt(fold_d, 60),
            "derivative_residual_divided_by_j": fmt(psi_prime(fold_x) / j),
            "log_Rstar_over_Rb": fmt(-fold_d, 60),
            "x_root_greater_than_x_fold": bool(exact > fold_x),
            "d_fold_negative": bool(fold_d < 0),
        }
    return record


def complex_fold_case(X, k=1):
    X, k = mp.mpf(X), int(k)
    h, z, d = 1 / X, mp.exp(-X), mp.exp(-2 * X)
    lam0, A0 = 2 * mp.pi * mp.j * k, mp.zeta(2)
    alpha0 = lam0 * (mp.log(4 * A0) / 2 - 2)
    omega0 = 2 * mp.sqrt(A0)

    def paired(alpha, omega):
        eps = h * (lam0 + alpha * h)
        A = mp.zeta(2 + eps)
        M = E2(eps) * mp.exp(-alpha * h + eps * mp.log(omega))
        H = 1 + mp.zeta(1 + eps) - M / eps
        x = z * omega
        T, Tx = tail(eps, x), tail(eps, x, 1)
        F = omega * omega * H + z * omega ** 3 * T - 2 * A - 2 * z * omega + z * z
        Fw = 2 * omega * H - omega * M + 3 * z * omega * omega * T + z * z * omega ** 3 * Tx - 2 * z
        return F, Fw

    alpha, omega = mp.findroot(
        paired, (alpha0, omega0), tol=mp.mpf("1e-145"), maxsteps=50,
    )
    F, Fw = paired(alpha, omega)
    eps = h * (lam0 + alpha * h)
    A, order = mp.zeta(2 + eps), 3 + eps
    x = z * omega
    deficit = mp.zeta(order) - mp.polylog(order, mp.exp(-x))
    square_root = mp.sqrt(A * A + 2 * deficit)
    original_relative = (x + A - square_root) / d - 1
    original_derivative = (1 - mp.polylog(order - 1, mp.exp(-x)) / square_root) / z
    Falpha = mp.diff(lambda alpha_var: paired(alpha_var, omega)[0], alpha)
    Fww = mp.diff(lambda omega_var: paired(alpha, omega_var)[1], omega)
    return {
        "scope": "local fold of the continued normal form; no global sheet claim",
        "k": k, "X": fmt(X),
        "alpha_leading": complex_record(alpha0),
        "alpha_exact": complex_record(alpha),
        "omega_leading": fmt(omega0, 50),
        "omega_exact": complex_record(omega),
        "alpha_leading_absolute_error": fmt(abs(alpha - alpha0)),
        "omega_leading_absolute_error": fmt(abs(omega - omega0)),
        "paired_equation_absolute_residual": fmt(abs(F)),
        "paired_derivative_absolute_residual": fmt(abs(Fw)),
        "original_relative_residual_absolute": fmt(abs(original_relative)),
        "original_derivative_residual_divided_by_z_absolute": fmt(abs(original_derivative)),
        "F_alpha": complex_record(Falpha),
        "F_omega_omega": complex_record(Fww),
        "fold_jacobian_absolute": fmt(abs(Falpha * Fww)),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--X", type=int, nargs="+", default=[40, 80])
    parser.add_argument("--dps", type=int, default=180)
    parser.add_argument("--skip-complex", action="store_true")
    parser.add_argument("--complex-X", type=int, default=40)
    args = parser.parse_args()
    mp.mp.dps = args.dps
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows = []
    for X in args.X:
        for lam in (-2, 0, 2):
            for eta in (-1, 0, 1):
                row = real_case(lam, eta, X)
                rows.append(row)
                print(json.dumps({key: row[key] for key in (
                    "lambda", "eta", "X", "first_relative_error",
                    "original_relative_residual", "positive_derivative_at_root"
                )}), flush=True)
    result = {
        "precision_decimal_digits": mp.mp.dps,
        "status": "numerical diagnostics, not interval-certified",
        "real_cases": rows,
    }
    if not args.skip_complex:
        result["local_complex_fold"] = complex_fold_case(args.complex_X)
        print(json.dumps(result["local_complex_fold"]), flush=True)
    target = args.output_dir / "joint_crossover_checks.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Wrote {target}", flush=True)


if __name__ == "__main__":
    main()
