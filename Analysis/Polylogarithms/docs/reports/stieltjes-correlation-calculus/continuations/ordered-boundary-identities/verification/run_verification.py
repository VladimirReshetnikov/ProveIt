#!/usr/bin/env python3
"""Run exact checks, or all ordinary numerical diagnostics as well.

The optional asymptotic replay propagates exact rational recurrences to b=120.
All generated JSON files are written beside their corresponding programs.
These programs are verification aids, not substitutes for the article's proofs.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def execute(name):
    result = subprocess.run([sys.executable, str(HERE / name)],
                            text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    print(name + ": passed", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true",
                        help="also run ordinary sums and numerical integrals")
    parser.add_argument("--asymptotics", action="store_true",
                        help="also replay the optional determinant asymptotics")
    args = parser.parse_args()
    import verify_ordered_boundary as ordered
    import verify_ordered_corollaries as corollaries
    import verify_beta_stieltjes as beta

    report = {
        "finite_cutoff": ordered.finite_exact_tests(),
        "partial_fractions": ordered.partial_fraction_tests(),
        "parity_coefficients": ordered.parity_tests(),
        "cutoff_generator_coefficients": ordered.cutoff_generator_tests(),
        "directional_table": ordered.anomaly_derivative_tests(),
        "digamma_master": corollaries.exact_F_derivatives(),
        "subtracted_Stieltjes_jets": corollaries.stieltjes_coefficients(),
        "beta_Bell_Leibniz": beta.exact_bell_checks(),
    }
    execute("verify_localization.py")
    execute("verify_gamma_exact.py")
    report["status"] = "passed"
    report["scope"] = "Exact finite algebra; see separate JSON files for scopes."
    if args.full:
        for name in ["verify_ordered_boundary.py", "verify_ordered_corollaries.py",
                     "verify_beta_stieltjes.py", "verify_gamma_integrals.py"]:
            execute(name)
        report["ordinary_numeric_diagnostics"] = "passed"
    if args.asymptotics:
        execute("verify_gamma_asymptotics.py")
        report["asymptotic_diagnostics"] = "passed"
    (HERE / "verification_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
