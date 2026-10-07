#!/usr/bin/env python3
"""Optional high-precision numerical diagnostics, separate from exact replay.

Requires mpmath. These finite computations do not prove asymptotic limits, a
remainder rate, effective inverse brackets, or literature priority.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import hashlib
import json
import sys

sys.dont_write_bytecode = True
from exact import VerificationError, load_json, validate_values, write_json, require


def run(data_dir, precision=85):
    try:
        import mpmath as mp
    except ImportError as exc:
        raise VerificationError("Optional diagnostics require mpmath; exact replay does not") from exc
    require(type(precision) is int and 50 <= precision <= 500, "precision must be between 50 and 500 decimal digits")
    mp.mp.dps = precision
    path = Path(data_dir)/"exact_values.json"
    values = validate_values(load_json(path))
    m, a, g4 = (list(map(int, values[key])) for key in ("m", "a", "four_gamma"))
    fmt = lambda x: mp.nstr(x, 36)
    I = mp.gamma(mp.mpf(1)/4)*mp.sqrt(mp.pi)/(4*mp.gamma(mp.mpf(3)/4))
    J = mp.gamma(mp.mpf(3)/4)*mp.sqrt(mp.pi)/mp.gamma(mp.mpf(1)/4)
    H, r, rho = 1/I, mp.sqrt(2)/I, 2*I
    C = mp.log(4*mp.sqrt(2)*mp.pi**mp.mpf("1.5")*r*r)
    c, d = (1+mp.pi)/16, (13-3*mp.pi)/48
    F = lambda x: mp.sqrt(2/mp.pi)*r**(4*x+2)*mp.gamma(x+1)**4/mp.sqrt(x)
    tolerance = mp.mpf("1e-"+str(precision//2-4))
    I_integral = mp.quad(lambda u: 1/mp.sqrt(1-u**4), [0, mp.mpf(".5"), mp.mpf(".9"), 1])
    J_integral = mp.quad(lambda u: u*u/mp.sqrt(1-u**4), [0, mp.mpf(".5"), mp.mpf(".9"), 1])
    require(abs(I-I_integral) < tolerance, "Numerical I integral mismatch")
    require(abs(J-J_integral) < tolerance, "Numerical J integral mismatch")
    require(abs(I*J-mp.pi/4) < tolerance, "Numerical beta normalization mismatch")
    def entropy(v):
        left, right = (1+v)/2, (1-v)/2
        return -(left*mp.log(left) if left else 0)-(right*mp.log(right) if right else 0)
    phi = 2*H*mp.quad(lambda u: (entropy(mp.sqrt(1-u**4))+2*mp.log(H*u))/mp.sqrt(1-u**4),
                      [0, mp.mpf(".5"), mp.mpf(".9"), 1])
    require(abs(phi-(4*mp.log(r)-4)) < tolerance, "Entropy free-energy normalization mismatch")
    ratios = []
    for n in (20, 40, 50, 80, 100, 160, 200, 500):
        b = mp.mpf(g4[n])/mp.mpf(4)**n
        classical = mp.power(2,3-2*n)*mp.gamma(4*n+2)/rho**(4*n+2)
        row = {"n": n, "m_over_F": fmt(mp.mpf(m[n])/F(n)),
            "n_times_log_comparison_error": fmt(n*(mp.log(mp.mpf(m[n])/b)-mp.log(mp.pi/2))),
            "n_times_relative_comparison_error": fmt(n*(mp.mpf(m[n])/b/(mp.pi/2)-1)),
            "n_times_relative_factorial_error": fmt(n*(mp.mpf(m[n])/F(n)-1)),
            "n_times_classical_factorial_error": fmt(n*((mp.pi/2)*b/F(n)-1)),
            "comparison_moment_over_gamma_template_minus_one": fmt(b/classical-1)}
        if n < len(a):
            row["a_over_F"] = fmt(mp.mpf(a[n])/F(n))
            row["n_times_cumulant_factorial_error"] = fmt(n*(mp.mpf(a[n])/F(n)-1))
            row["n3_times_one_minus_a_over_m"] = fmt(n**3*(1-mp.mpf(a[n])/m[n]))
        ratios.append(row)
    regularization = []
    for eps in map(mp.mpf, [".1", ".03", ".01", ".003", ".001"]):
        cutoff = eps/H
        bracket = (mp.sqrt(1-cutoff**4)-1)/cutoff-J+mp.quad(
            lambda u: u*u/mp.sqrt(1-u**4), [0,cutoff])
        value = bracket/(4*H)
        regularization.append({"epsilon": fmt(eps), "regularized_quarter_integral": fmt(value),
            "error_from_minus_pi_over_16": fmt(value+mp.pi/16),
            "error_over_epsilon_cubed": fmt((value+mp.pi/16)/eps**3)})
    inverse = []
    model = lambda x: 4*x*mp.log(r*x/mp.e)+mp.mpf("1.5")*mp.log(x)+C+d/x
    for x in map(mp.mpf, ["100", "1000", "10000", "1000000"]):
        L = model(x)
        t = L/(4*mp.lambertw(r*L/(4*mp.e)))
        D = 4*mp.log(r*t)
        delta0 = -(mp.mpf("1.5")*mp.log(t)+C)/D
        delta1 = -(2*delta0**2+mp.mpf("1.5")*delta0+d)/(t*D)
        xi = t+delta0+delta1
        inverse.append({"smooth_model_root": fmt(x), "second_center": fmt(xi),
            "root_minus_center": fmt(x-xi),
            "root_error_times_t_log_t": fmt((x-xi)*t*mp.log(t)),
            "root_error_times_t2_log_t": fmt((x-xi)*t*t*mp.log(t)),
            "model_residual_times_t2": fmt((model(xi)-L)*t*t)})
    return {"schema": "report199-numerical-diagnostics-v1",
        "status": "PASS", "scope": "Numerical diagnostics only; not proofs or effective error certificates.",
        "mpmath_version": mp.__version__, "decimal_working_precision": precision,
        "exact_values_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "constants": {"I": fmt(I), "J": fmt(J), "peak_height_H": fmt(H), "r": fmt(r),
            "entropy_free_energy": fmt(phi), "comparison_correction": fmt(-mp.pi/16),
            "factorial_correction": fmt(-c), "inverse_d": fmt(d),
            "expected_n3_cumulant_gap": fmt(2/r**4)},
        "moment_ratios": ratios, "regularized_integral": regularization,
        "smooth_inverse": inverse}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path(__file__).resolve().parents[1]/"data")
    parser.add_argument("--output", type=Path, help="Optional destination outside the manifest-covered package")
    parser.add_argument("--precision", type=int, default=85)
    args = parser.parse_args()
    try:
        result = run(args.data, args.precision)
        if args.output is not None:
            write_json(args.output, result)
        print(json.dumps(result, sort_keys=True, indent=2))
    except (VerificationError, OSError) as exc:
        parser.exit(1, f"Numerical diagnostic failed: {exc}\n")


if __name__ == "__main__":
    main()
