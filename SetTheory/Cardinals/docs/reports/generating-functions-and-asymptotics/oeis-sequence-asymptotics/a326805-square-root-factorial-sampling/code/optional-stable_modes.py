#!/usr/bin/env python3
"""Optional Gaussian completed-line diagnostics, without interval certification.

Quick: python optional/stable_modes.py
Full:  python optional/stable_modes.py --full
Needs mpmath. Nothing is written unless --output PATH is supplied.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))


def completed_mode(mp, L, m, cut):
    """Numerically truncate F_m minus its negative ray at |u|,r=cut."""
    imaginary = mp.j
    root = mp.exp(imaginary * mp.pi / 4)
    q = 4 * mp.pi * m
    alpha = mp.mpf(1) / (8 * m)
    y = mp.lambertw(q * mp.exp(L)) / q
    center = alpha + imaginary * y

    def integrand(u):
        z = center + root * u
        return 2 * root * mp.exp(L * z + imaginary * q * z * z / 2) * mp.rgamma(z)

    def negative_ray(r):
        z = -root * r
        return 2 * root * mp.exp(L * z + imaginary * q * z * z / 2) * mp.rgamma(z)

    nodes = sorted(set([-cut, cut] + [n for n in [-8, -4, -2, 0, 2, 4, 8] if -cut < n < cut]))
    negative_nodes = sorted(set([mp.mpf(0), mp.mpf(1) / max(1, L), cut] +
                                [mp.mpf(n) for n in [1, 2, 4, 8] if n < cut]))
    full = mp.quad(integrand, nodes)
    negative = mp.quad(negative_ray, negative_nodes)
    return full - negative


def evaluate_coefficient(mp, polynomial):
    answer = mp.mpc(0)
    for power, (real, imag) in polynomial.items():
        real_value = mp.mpf(real.numerator) / real.denominator
        imag_value = mp.mpf(imag.numerator) / imag.denominator
        answer += mp.mpc(real_value, imag_value) / mp.pi ** power
    return answer


def run(log_x_values, modes, terms, cuts, digits):
    import mpmath as mp
    from exact_coefficients import coeffs

    rows = []
    with mp.workdps(digits):
        for m in modes:
            coefficients = [evaluate_coefficient(mp, polynomial)
                            for polynomial in coeffs(max(terms) - 1, m)]
            for input_L in log_x_values:
                L = mp.mpf(input_L)
                q = 4 * mp.pi * m
                alpha = mp.mpf(1) / (8 * m)
                beta = mp.mpf(1) / 2 - alpha
                y = mp.lambertw(q * mp.exp(L)) / q
                phase = q * y * y / 2 + y - mp.pi / (32 * m)
                envelope = 4 * mp.exp(alpha * L) * y ** beta / mp.sqrt(q)
                values = [2 * mp.re(completed_mode(mp, L, m, mp.mpf(cut))) for cut in cuts]
                reference = values[-1]
                expansions = []
                for term_count in terms:
                    polynomial = mp.fsum(coefficients[j] / y ** j for j in range(term_count))
                    approximation = -envelope * mp.im(mp.exp(mp.j * phase) * polynomial)
                    normalized_error = (reference - approximation) / envelope
                    expansions.append({"terms_K": term_count,
                                       "asymptotic_value": mp.nstr(approximation, 25),
                                       "normalized_error": mp.nstr(normalized_error, 20),
                                       "scaled_error_y_to_K": mp.nstr(normalized_error * y ** term_count, 20)})
                rows.append({"log_x": input_L, "mode_m": m,
                             "saddle_y": mp.nstr(y, 25), "envelope_A": mp.nstr(envelope, 25),
                             "truncated_mode_values": [{"cutoff": cut, "two_real_J": mp.nstr(value, 30)}
                                                       for cut, value in zip(cuts, values)],
                             "cutoff_change_normalized_by_A": mp.nstr((values[-1] - values[0]) / envelope, 12),
                             "expansions": expansions})
    return {"kind": "completed_line_floating_diagnostics", "interval_certified": False,
            "qualification": "Finite-cutoff mpmath quadrature and floating coefficient evaluation. "
                             "Cutoff agreement and scaled errors are consistency diagnostics, "
                             "not certified quadrature bounds or a proof of the asymptotic remainder.",
            "decimal_precision": digits, "mpmath_version": mp.__version__,
            "coefficient_source": "code/exact_coefficients.py: coeffs(K-1,m)", "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-x", nargs="+", type=int, default=[20, 80], help="Integer log(x) values, 2..2000")
    parser.add_argument("--modes", nargs="+", type=int, default=[1, 2], help="Positive modes, 1..32")
    parser.add_argument("--terms", nargs="+", type=int, default=[1, 2, 3], help="Numbers of terms K, 1..7")
    parser.add_argument("--cuts", nargs=2, type=int, default=[10, 12], help="Two increasing Gaussian cutoffs, 6..40")
    parser.add_argument("--digits", type=int, default=50, help="Decimal precision, 30..300")
    parser.add_argument("--full", action="store_true", help="Use L=20,40,80,120,200,400,800; m=1,2,3; cuts=14,16; 70 digits")
    parser.add_argument("--output", type=Path, help="Also write JSON to this explicit path")
    args = parser.parse_args()
    try:
        if args.full:
            args.log_x, args.modes, args.cuts, args.digits = [20, 40, 80, 120, 200, 400, 800], [1, 2, 3], [14, 16], 70
        if not all(2 <= L <= 2000 for L in args.log_x):
            raise ValueError("Every --log-x must lie in 2..2000")
        if not all(1 <= m <= 32 for m in args.modes):
            raise ValueError("Every --modes value must lie in 1..32")
        if not all(1 <= K <= 7 for K in args.terms):
            raise ValueError("Every --terms value must lie in 1..7")
        if not 6 <= args.cuts[0] < args.cuts[1] <= 40:
            raise ValueError("Use two increasing --cuts between 6 and 40")
        if not 30 <= args.digits <= 300:
            raise ValueError("--digits must lie in 30..300")
        result = run(args.log_x, args.modes, args.terms, args.cuts, args.digits)
        rendered = json.dumps(result, indent=2) + "\n"
        if args.output is not None:
            args.output.write_text(rendered, encoding="utf-8")
        print(rendered, end="")
        return 0
    except (ImportError, OSError, ValueError, ArithmeticError) as exc:
        print(json.dumps({"status": "error", "message": str(exc), "interval_certified": False}))
        return 2


if __name__ == "__main__":
    sys.exit(main())
