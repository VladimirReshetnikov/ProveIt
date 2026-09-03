#!/usr/bin/env python3
"""Generate exact and numerical tables used by the LaTeX report."""
from pathlib import Path
import csv
import sympy as sp
from rvachev_polynomial_representation import (
    t,
    sparse_coefficients_fast,
    sparse_coefficients_recurrence,
    pair_compressed_coefficients,
    annihilator_coefficients,
    annihilator_mass,
    central_basis_determinant,
    verify_monomial_fast,
    h_operator_series,
    run_internal_exact_checks,
)

OUT = Path(__file__).resolve().parent


def main() -> None:
    run_internal_exact_checks(10)

    # Exact monomial coefficients through degree 8.
    with (OUT / "monomial_sparse_coefficients.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["degree", "scale", "center", "coefficient_of_raw_up"])
        for d in range(9):
            rep = sparse_coefficients_fast(t**d, d=d)
            for k, c in rep.as_pairs():
                w.writerow([d, rep.scale, k, str(c)])

    # Numerical inverse-Fourier residuals.  These intentionally reveal the
    # cancellation of the minimal endpoint basis at higher degree.
    with (OUT / "numerical_residuals.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["degree", "max_grid_error", "grid_points", "cutoff", "gauss_nodes_per_lobe"])
        for d in range(7):
            err = verify_monomial_fast(d, grid_points=17, cutoff=80, nodes_per_lobe=48)
            w.writerow([d, f"{err:.17e}", 17, 80, 48])

    # Exact determinant evidence for the central-basis conjecture.
    with (OUT / "central_basis_determinants.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["degree", "determinant"])
        for d in range(13):
            w.writerow([d, str(central_basis_determinant(d))])

    # Low annihilator coefficients and truncated H_d operators.
    with (OUT / "operator_and_annihilator_table.txt").open("w") as f:
        for d in range(1, 9):
            low = annihilator_coefficients(d, truncate=d + 1)
            if len(low) < d + 2:
                low += [0] * (d + 2 - len(low))
            f.write(f"d={d}\n")
            f.write(f"A_d(1)={annihilator_mass(d)}\n")
            f.write(f"a_0..a_(d+1)={low}\n")
            f.write(f"H_d(z) mod z^(d+1)={sp.expand(h_operator_series(d,d))}\n\n")

    # Human-readable summary for quick audit.
    with (OUT / "exact_checks.txt").open("w") as f:
        f.write("All one-cell and multi-cell fast-vs-full recurrence checks passed through d=10.\n")
        f.write("Polynomiality certificate checks passed through d=10.\n")
        f.write("Degree-(d+1) certificate normalization checks passed through d=10.\n")
        f.write("Central determinant checks were exact over the integers through d=12.\n")


if __name__ == "__main__":
    main()
