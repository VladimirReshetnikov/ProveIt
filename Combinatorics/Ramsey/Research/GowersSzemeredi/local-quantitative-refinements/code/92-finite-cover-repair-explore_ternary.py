#!/usr/bin/env python3
"""Optional numerical exploration of the ternary quartic conjecture.

Requires NumPy and SciPy. This script is NOT a proof of the global maximum.
It reads the exact Laurent coefficients produced by verify_exact.py and
uses an analytic gradient in a phase-only, multistart BFGS search.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import platform
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--starts", type=int, default=30)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    if args.starts < 1:
        parser.error("--starts must be positive")
    try:
        import numpy as np
        import scipy
        from scipy.optimize import minimize
    except ImportError as error:
        raise SystemExit("Install NumPy and SciPy for this optional numerical experiment") from error
    root = Path(__file__).resolve().parent
    certificate = json.loads((root / "data/ternary_quartic_certificate.json").read_text())
    exponents = np.asarray([m["powers"] for m in certificate["monomials"]], dtype=float)
    zeta = complex(-0.5, np.sqrt(3)/2)
    coefficients = np.asarray([m["coefficient"][0] + m["coefficient"][1]*zeta
                               for m in certificate["monomials"]], dtype=complex)
    coefficients /= certificate["cube_count"]

    def objective_and_gradient(theta):
        terms = coefficients * np.exp(1j * (exponents @ theta))
        return -float(terms.real.sum()), exponents.T @ terms.imag

    rng = np.random.default_rng(args.seed)
    records = []
    best = None
    for index in range(args.starts):
        initial = np.zeros(9) if index == 0 else rng.uniform(-np.pi, np.pi, 9)
        result = minimize(objective_and_gradient, initial, jac=True, method="BFGS",
                          options={"gtol": 1e-10, "maxiter": 1000})
        energy = -float(result.fun)
        row = {"start": index, "energy": energy, "success": bool(result.success),
               "message": str(result.message), "iterations": int(result.nit),
               "gradient_norm": float(np.linalg.norm(result.jac)),
               "phases_radians": result.x.tolist()}
        records.append(row)
        if best is None or energy > best["energy"]:
            best = row
    output = args.output or root / "data/ternary_numerical_experiment.json"
    report = {"status": "numerical evidence only; no global-optimality certificate",
              "seed": args.seed, "starts": args.starts,
              "python": platform.python_version(), "numpy": np.__version__,
              "scipy": scipy.__version__, "best": best, "runs": records}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Largest numerical energy: {best['energy']:.17g}")
    print(f"Exact lower-bound comparison 11/27: {11/27:.17g}")
    print(f"Recorded all {args.starts} optimizer statuses in {output}")
    print("No global maximum has been certified by this search.")


if __name__ == "__main__":
    main()
