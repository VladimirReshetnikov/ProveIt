"""Reproduce the small Lerch scan and proposed bifurcation coordinates.

All results from this script are numerical diagnostics, not certificates.
It uses ordinary SciPy quadrature on a finite v = log(x) interval. Reported
quadrature error estimates exclude the omitted infinite tails and are not
rigorous bounds. The exact endpoint signs have a separate stdlib verifier.

Run from any working directory; by default the two JSON files are written
in the package results directory. Use --output-dir to select another destination, or
--bifurcations-only to regenerate only the two candidate solves.
"""

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq, root
from scipy.special import zeta

GAMMA = np.euler_gamma
V_LOWER = -60.0
AX_UPPER = 100.0
QUAD_ABS = 2e-12
QUAD_REL = 2e-12
QUAD_LIMIT = 400


def Q(n, v):
    """Q_n(v), defined by exp(v*t)/Gamma(1+t), for n = 3 or 4."""
    y = v + GAMMA
    if n == 3:
        return y**3 - 3*zeta(2, 1)*y + 2*zeta(3, 1)
    if n == 4:
        return (y**4 - 6*zeta(2, 1)*y*y + 8*zeta(3, 1)*y
                + 3*zeta(2, 1)**2 - 6*zeta(4, 1))
    raise ValueError(n)


def integral(n, a, log_delta, a_derivative=0, log_delta_derivative=0):
    """Return (quadrature value, heuristic error estimate) for F or its derivatives.

    F = (-1)^(n+1) D_{n,1}^rho.  The stable second coordinate is
    log_delta = log(1-rho); -infinity denotes rho = 1.  Calculations use
    delta directly instead of subtracting the nearly unit value of rho.
    """
    if a <= 0 or log_delta > 0 or log_delta_derivative not in (0, 1):
        raise ValueError("Need a > 0, log_delta <= 0, and derivative order 0 or 1.")
    delta = np.exp(log_delta)
    rho = -np.expm1(log_delta)

    def integrand(v):
        x = np.exp(v)
        den = delta + rho * (-np.expm1(-x))
        value = ((-1)**a_derivative
                 * np.exp((2+a_derivative)*v-a*x)*Q(n, v)/den)
        if log_delta_derivative:
            value *= -delta*np.exp(-x)/den
        return value

    upper = np.log(AX_UPPER/a)
    points = [log_delta] if V_LOWER < log_delta < upper else []
    return quad(integrand, V_LOWER, upper, points=points,
                epsabs=QUAD_ABS, epsrel=QUAD_REL, limit=QUAD_LIMIT)


def F(n, a, rho, der=0):
    """Compatibility wrapper accepting rho rather than log(1-rho)."""
    log_delta = np.log1p(-rho) if rho < 1 else -np.inf
    return integral(n, a, log_delta, a_derivative=der)[0]


def roots(n, log_delta):
    """Numerical sign-change scan; this is not a complete-root certificate."""
    mesh = np.unique(np.concatenate((
        np.geomspace(.05, np.exp(n), 180), np.linspace(.5, 2.5, 220))))
    values = [integral(n, a, log_delta)[0] for a in mesh]
    return [brentq(lambda a: integral(n, a, log_delta)[0], a, b, xtol=2e-12)
            for a, b, u, v in zip(mesh, mesh[1:], values, values[1:])
            if u*v < 0]


def scan():
    """Regenerate exactly the original ten-case quadrature scan grid."""
    output = []
    for n in (3, 4):
        for delta in (1e-3, 1e-4, 1e-5, 1e-6, 0.0):
            log_delta = np.log(delta) if delta else -np.inf
            found_roots = roots(n, log_delta)
            diagnostics = [integral(n, a, log_delta) for a in found_roots]
            row = dict(
                n=n, rho=float(-np.expm1(log_delta)), delta=delta,
                roots=found_roots,
                residuals=[value for value, _ in diagnostics],
                quad_error_estimates=[error for _, error in diagnostics],
                status="Ordinary quadrature; finite sign-change scan; roots and counts not certified.",
                v_truncation_lower=V_LOWER,
                a_times_exp_v_upper=AX_UPPER,
                quadrature_settings=dict(epsabs=QUAD_ABS, epsrel=QUAD_REL,
                                         limit=QUAD_LIMIT),
                limitations="Omitted tails are not bounded; quadrature estimates are heuristic.",
            )
            output.append(row)
            print(json.dumps(row), flush=True)
    return output


def bifurcation_candidates():
    """Solve F = F_a = 0 in the coordinates (a, log(1-rho))."""
    output = []
    for n, guess in ((3, (1.05, -11.5)), (4, (1.20, -16.5))):
        def equations(z):
            a, ell = z
            return [integral(n, a, ell)[0],
                    integral(n, a, ell, a_derivative=1)[0]]

        def jacobian(z):
            a, ell = z
            return [
                [integral(n, a, ell, a_derivative=1)[0],
                 integral(n, a, ell, log_delta_derivative=1)[0]],
                [integral(n, a, ell, a_derivative=2)[0],
                 integral(n, a, ell, a_derivative=1,
                          log_delta_derivative=1)[0]],
            ]

        solution = root(equations, guess, jac=jacobian, method="hybr", tol=1e-9)
        a, ell = map(float, solution.x)
        value, value_error = integral(n, a, ell)
        first_a, first_error = integral(n, a, ell, a_derivative=1)
        second_a, second_error = integral(n, a, ell, a_derivative=2)
        first_ell, ell_error = integral(n, a, ell, log_delta_derivative=1)
        row = dict(
            n=n, a=a, rho=float(-np.expm1(ell)), delta=float(np.exp(ell)),
            log_delta=ell, solver_coordinates=["a", "log(1-rho)"],
            initial_guess=list(guess), converged=bool(solution.success),
            solver_message=str(solution.message), nfev=int(solution.nfev),
            residual=[value, first_a], second_a=second_a,
            derivative_log_delta=first_ell,
            quad_error_estimates=dict(F=value_error, F_a=first_error,
                                      F_aa=second_error, F_log_delta=ell_error),
            v_truncation=[V_LOWER, float(np.log(AX_UPPER/a))],
            quadrature_settings=dict(epsabs=QUAD_ABS, epsrel=QUAD_REL,
                                     limit=QUAD_LIMIT),
            status="Ordinary quadrature and local nonlinear solve; not certified.",
            limitations=("Tail errors not certified; quadrature estimates are heuristic; "
                         "no uniqueness, multiplicity, or transversality certificate."),
        )
        output.append(row)
        print(json.dumps(row), flush=True)
        if not solution.success:
            raise RuntimeError(f"Candidate solve for n={n} did not converge: {solution.message}")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1]/"results")
    parser.add_argument("--bifurcations-only", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if not args.bifurcations_only:
        (args.output_dir/"lerch_integral_scan.json").write_text(
            json.dumps(scan(), indent=2)+"\n", encoding="utf-8")
    (args.output_dir/"lerch_numerical_bifurcations.json").write_text(
        json.dumps(bifurcation_candidates(), indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
