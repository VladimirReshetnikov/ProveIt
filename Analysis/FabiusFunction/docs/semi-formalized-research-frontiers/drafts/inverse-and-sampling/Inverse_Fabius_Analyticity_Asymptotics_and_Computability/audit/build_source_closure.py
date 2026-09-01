#!/usr/bin/env python3
"""Build or verify the exact 23-input TeX source-closure ledger."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[1]
OUTPUT = PACKAGE / "SOURCE_CLOSURE.sha256"

INPUTS = (
    "./inverse_fabius_theory.tex",
    "../../../../fabius-notation.tex",
    "./chapters/00_scope_and_platform.tex",
    "./chapters/01_analyticity_and_elementarity.tex",
    "./chapters/02_inverse_iterates.tex",
    "./chapters/03_inverse_germs_and_deconvolution.tex",
    "./chapters/04_endpoint_all_orders.tex",
    "./chapters/05_dyadic_self_sampling.tex",
    "./chapters/06_computability.tex",
    "./chapters/07_certification_and_provenance.tex",
    "./chapters/09_references.tex",
    "./assets/self-sampling/generated/appell_polynomials.tex",
    "./assets/self-sampling/generated/harmonic_tail_table.tex",
    "./assets/self-sampling/generated/quadrature_table_display.tex",
    "./assets/inverse-germs/figures/quarter_quantile_richardson.png",
    "./assets/endpoint/wright-omega/figures/carrier_comparison.png",
    "./assets/endpoint/wright-omega/figures/scaled_residuals.png",
    "./assets/endpoint/all-orders/figures/endpoint_error_plot.png",
    "./assets/endpoint/dyadic-completion/figures/psi_periodic.png",
    "./assets/endpoint/dyadic-completion/figures/dyadic_tail_convergence.png",
    "./assets/self-sampling/figures/defect_profiles.png",
    "./assets/self-sampling/figures/quadrature_weights.png",
    "./assets/self-sampling/figures/appell_roots.png",
)


def input_path(display_path: str) -> Path:
    return (PACKAGE / display_path).resolve()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ledger_bytes() -> bytes:
    if len(INPUTS) != 23 or len(set(INPUTS)) != 23:
        raise ValueError("source closure must contain exactly 23 distinct inputs")
    rows: list[str] = []
    for display_path in INPUTS:
        path = input_path(display_path)
        if not path.is_file():
            raise FileNotFoundError(f"missing source-closure input: {display_path}")
        rows.append(f"{sha256(path)}  {display_path}\n")
    return "".join(rows).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the ledger with the current 23 source inputs",
    )
    args = parser.parse_args()
    payload = ledger_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_bytes() != payload:
            print(f"FAILED: stale source-closure ledger: {OUTPUT}")
            return 1
        print(f"source closure: PASS (23 inputs; ledger SHA-256 {digest})")
    else:
        OUTPUT.write_bytes(payload)
        print(f"wrote: {OUTPUT}")
        print(f"inputs: 23")
        print(f"ledger SHA-256: {digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
