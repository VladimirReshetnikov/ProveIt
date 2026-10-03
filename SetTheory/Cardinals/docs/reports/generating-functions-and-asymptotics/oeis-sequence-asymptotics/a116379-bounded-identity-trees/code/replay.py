#!/usr/bin/env python3
"""Offline reproducibility checks. Requires Python 3.10+ and mpmath 1.3.0."""
import argparse
import json
import platform
import time
from pathlib import Path
import mpmath as mp
from check_identity import DATA, positive_product, newton_recurrence
from identity_allorders import compute as jets, gamma_corrections
from identity_inverse import compute as inverse, inverse_coefficients, pure_log_polynomials


def close(a, b, tolerance="1e-60"):
    if abs(mp.mpf(a)-mp.mpf(b)) > mp.mpf(tolerance):
        raise AssertionError(f"Numerical disagreement > {tolerance}: {a} vs {b}")


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def formula_tests(src):
    """Closed-form low-order tests plus explicit finite-model zero-extension."""
    mp.mp.dps = 90
    lam = -mp.log(mp.mpf(src["rho"]))
    D = list(map(mp.mpf, src["corrections"]))
    p = mp.mpf("1.5")
    b = list(map(mp.mpf, src["puiseux"]))
    close(D[1], mp.mpf(3)/8-p*b[3]/b[1])
    close(D[2], mp.mpf(25)/128-mp.mpf(45)/16*b[3]/b[1]+mp.mpf(15)/4*b[5]/b[1])
    E = inverse_coefficients(lam, D, 4, 4)
    L2 = D[2]-D[1]**2/2
    close(E[1], -D[1]/lam)
    close(E[2], -p*D[1]/lam**2-L2/lam)
    P = pure_log_polynomials(lam, D, 4, 4)
    for h in map(mp.mpf, [0, 1, 2, 5]):
        close(P[0].evaluate(h), p*p*h-lam*D[1])
        close(P[1].evaluate(h), -p**3*h*h/2+p**3*h+p*lam*D[1]*(h-1)-lam**2*L2)
    assert all(len(polynomial.coefficients) <= k+1 for k, polynomial in enumerate(P, 1))
    # Same finite Q_2, written two ways: higher stored corrections MUST be
    # discarded by R=2; a degree-six representation with zero tails is equal.
    E2 = inverse_coefficients(lam, D, 2, 6)
    padded = D[:3] + [mp.mpf(0)]*4
    Epad = inverse_coefficients(lam, padded, 6, 6)
    P2 = pure_log_polynomials(lam, D, 2, 6)
    Ppad = pure_log_polynomials(lam, padded, 6, 6)
    assert E2 == Epad and P2 == Ppad
    assert E2[3] != E[3], "Distinct smooth models must not silently share E_3"
    assert all(x == 0 for x in inverse_coefficients(lam, D, 0, 6))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=DATA.parent/"replay-output")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    reference_counts = json.loads((DATA/"identity-checks.json").read_text())
    counts = {}
    for d in (2, 3, 4):
        a = positive_product(d, 400)
        assert a == newton_recurrence(d, 400)
        assert a == reference_counts[str(d)]["terms"]
        counts[str(d)] = {"N": 400, "both_integer_routes_agree": True, "terms": a}
        print(f"PASS exact counts: d={d}, all n=0,...,400", flush=True)
    save(args.output_dir/"exact-counts.json", counts)

    reference_jets = json.loads((DATA/"identity-allorders-checks.json").read_text())
    all_jets, high = [], []
    for d in (3, 4):
        rows = [jets(d, N, precision, 4, route) for N, precision, route in
                [(200, 70, "sum"), (400, 110, "sum"), (250, 80, "differentiate")]]
        for row in rows:
            ref = next(x for x in reference_jets if x["d"] == d and x["N"] == row["N"])
            for field in ("rho", "tau", "C"):
                close(row[field], ref[field])
                close(row[field], rows[1][field])
            for field in ("puiseux", "corrections"):
                for x, y, z in zip(row[field], ref[field], rows[1][field]):
                    close(x, y)
                    close(x, z)
            close(row["jet_residual_max"], 0)
            close(row["linear_slope_check_max"], 0)
            for check in row["checks"]:
                refcheck = next(x for x in ref["checks"] if x["n"] == check["n"])
                for x, y in zip(check["relative_residual_by_order"], refcheck["relative_residual_by_order"]):
                    close(x, y)
                # Actual signed values are retained; this is not an absolute
                # error convention and no exact-rounding inference is made.
                assert all(s == -1 for s in check["residual_sign_by_order"])
        all_jets.extend(rows)
        high.append(rows[1])
        formula_tests(rows[1])
        print(f"PASS jets d={d}: both nested routes and three truncation/precision runs agree within 1e-60", flush=True)
    close(gamma_corrections(mp.mpf(".5"), 2)[1], mp.mpf(3)/8)
    close(gamma_corrections(mp.mpf(".5"), 2)[2], mp.mpf(25)/128)
    save(args.output_dir/"allorders-checks.json", all_jets)

    reference_inverse = json.loads((DATA/"identity-inverse-checks.json").read_text())
    inverses, extended = [], []
    for src in high:
        row = inverse(src, 4, 4, 90)
        ref = next(x for x in reference_inverse if x["d"] == src["d"])
        close(row["lambda"], ref["lambda"])
        for x, y in zip(row["inverse_coefficients"], ref["inverse_coefficients"]):
            close(x, y)
        for check, refcheck in zip(row["checks"], ref["checks"]):
            close(check["model_inverse_minus_exact_n"], refcheck["model_inverse_minus_exact_n"])
            close(check["model_log_equation_residual"], 0)
            assert mp.mpf(check["model_log_derivative"]) > 0
            for field in ("inverse_series_minus_model_by_order", "inverse_series_minus_exact_n_by_order"):
                for x, y in zip(check[field], refcheck[field]):
                    close(x, y)
        pure_errors = [abs(mp.mpf(c["pure_log_minus_model_by_order"][-1])) for c in row["checks"]]
        assert all(x > y for x, y in zip(pure_errors, pure_errors[1:]))
        inverses.append(row)
        extended.append(inverse(src, 2, 6, 90))
        extended.append(inverse(src, 0, 4, 90))
        print(f"PASS inverse d={src['d']}: saved R=K=4 results, pure-log formulas, R=2/K=6 zero-extension, R=0 carrier", flush=True)
    save(args.output_dir/"inverse-checks.json", inverses)
    save(args.output_dir/"inverse-extended-checks.json", extended)
    summary = {"status": "PASS", "python": platform.python_version(),
               "mpmath": mp.__version__, "elapsed_seconds": round(time.monotonic()-started, 3),
               "exact_count_routes": "positive product and independently coded Newton recurrence",
               "numerical_comparison_absolute_tolerance": "1e-60",
               "limitations": "Numerical stability checks; not interval certificates or exact rounding guarantees"}
    save(args.output_dir/"summary.json", summary)
    print(f"PASS all checks in {summary['elapsed_seconds']} seconds; results in {args.output_dir}", flush=True)


if __name__ == "__main__":
    main()
