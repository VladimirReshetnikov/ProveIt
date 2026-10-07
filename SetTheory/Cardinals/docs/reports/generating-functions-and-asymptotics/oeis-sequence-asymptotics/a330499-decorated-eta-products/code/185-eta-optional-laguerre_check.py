#!/usr/bin/env python3
"""Independent finite-jet associated-Laguerre recurrence diagnostic, J=0,1,2,3."""
import sys
sys.dont_write_bytecode = True
import mpmath as mp
from _common import BOUNDARY, emit_json, exact_inputs, odd_sigma, parser, require
from _mp import constants, decimal, scaled_exact


def laguerre(n, alpha, x):
    require(n >= 0, "Laguerre degree must be nonnegative")
    u, v = mp.mpf(1), 1 + alpha - x
    if n == 0:
        return u
    for k in range(1, n):
        u, v = v, ((2 * k + 1 + alpha - x) * v - (k + alpha) * u) / (k + 1)
    return v


def approximants(n, modes=11):
    # This finite-jet calculation does not call the harmonic H0/H1/H2 formula.
    mu, _, _ = constants()
    predictions = [mp.mpf(0) for _ in range(4)]
    for m in range(1, modes + 1):
        a = 2 * mp.pi**2 * m
        A = a / mu
        jets = [mp.mpf(1), a * mu / 6, mu**2 * (a*a / 72 - a / 24),
                mu**3 * (7*a / 180 - a*a / 144 + a**3 / 1296)]
        running = mp.mpf(0)
        for j in range(4):
            running += jets[j] * laguerre(n, -j - 1, A)
            predictions[j] -= mp.mpf(odd_sigma(m)) / m * mp.exp(-A) * running
    return [value * mp.mpf(n)**mp.mpf(".75") for value in predictions]


def run(nmax=2000, dps=60, standalone=False):
    require(50 <= nmax <= 2000 and 50 <= dps <= 100, "bounded range: 50<=max-n<=2000, 50<=dps<=100")
    values, engine = exact_inputs(nmax, standalone)
    samples = sorted({n for n in (50, 100, 200, 400, 800, 1000, 2000, nmax) if n <= nmax})
    rows = []
    with mp.workdps(dps):
        for n in samples:
            actual, predictions = scaled_exact(values[n], n), approximants(n)
            errors = [v - actual for v in predictions]
            require(all(abs(v) < mp.mpf(".1") for v in errors), f"Laguerre finite error regression at n={n}")
            limit = mp.mpf(".01") if n < 100 else mp.mpf(".001")
            require(abs(errors[3]) < limit, f"degree-three finite-jet regression at n={n}")
            rows.append({"n": n, "scaled_error": decimal(actual),
                         "predictions_J0_to_J3": [decimal(v) for v in predictions],
                         "errors_J0_to_J3": [decimal(v) for v in errors]})
    return {"schema_version": 1, "status": "PASS", "diagnostic": "laguerre_finite_jet",
            "max_n": nmax, "precision_dps": dps, "eta_modes": 11,
            "jet_degrees": [0, 1, 2, 3], "exact_input_engine": engine, "rows": rows,
            "checks": {"all_absolute_scaled_errors_limit_exclusive": "0.1",
                       "J3_absolute_scaled_error_limit_exclusive_n_below_100": "0.01",
                       "J3_absolute_scaled_error_limit_exclusive_n_at_least_100": "0.001"},
            "versions": {"mpmath": mp.__version__}, "boundary": BOUNDARY}


def main():
    p = parser(__doc__)
    p.add_argument("--max-n", type=int, default=2000)
    p.add_argument("--dps", type=int, default=60)
    p.add_argument("--standalone", action="store_true")
    args = p.parse_args()
    emit_json(run(args.max_n, args.dps, args.standalone), args.output)


if __name__ == "__main__":
    main()
