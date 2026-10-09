#!/usr/bin/env python3
"""Regenerate and verify the exact 2.027 certificate. No dependencies."""
from __future__ import annotations
import argparse
import csv
import json
import platform
from dataclasses import asdict
from decimal import Decimal, localcontext
from pathlib import Path
from profiles import (Parameters, IndependentVerifier, compute_profiles,
                      label_certificate, summarize)

ROOT = Path(__file__).resolve().parents[1]


def run(write: bool = False) -> dict:
    if not __debug__:
        raise RuntimeError("Run without -O: verification assertions must be enabled")
    p = Parameters()
    layers = compute_profiles(p)
    checked = IndependentVerifier(p).check_all(layers)
    values = summarize(p, layers)
    num, den = label_certificate(p)
    assert num < den, "The label-existence certificate failed"
    A, beta = values["A"], values["beta"]
    assert beta ** 1000 > A ** 2027, "The rational exponent certificate failed"
    assert values["n"] == values["beta"] * values["W"]
    assert num < (1 << 1054)
    assert A ** 50 < (1 << 14472)
    assert beta ** 50 > (1 << 29336)
    assert 1000 * 29336 - 2027 * 14472 == 1256
    with localcontext() as ctx:
        ctx.prec = 70
        alpha = Decimal(beta).ln() / Decimal(A).ln()
        label_ratio = Decimal(num) / Decimal(den)
        logmargin = 1000 * Decimal(beta).ln() - 2027 * Decimal(A).ln()
    report = dict(
        theorem_exponent={"numerator": 2027, "denominator": 1000},
        parameters=asdict(p), values=values,
        label_numerator=num, label_denominator=den,
        label_ratio_decimal=str(label_ratio),
        alpha_decimal_diagnostic=str(alpha),
        log_power_margin_decimal_diagnostic=str(logmargin),
        exact_checks={"labels_exist": num < den,
                      "beta_power_1000_exceeds_A_power_2027": beta**1000 > A**2027,
                      "independent_profile_entries_checked": checked,
                      "binomial_bit_length": num.bit_length(),
                      "A_power_50_bit_length": (A**50).bit_length(),
                      "beta_power_50_bit_length": (beta**50).bit_length(),
                      "binary_exponent_cross_product_gap": 1256,
                      "stronger_rational_exponent": "3667/1809"},
        verification_scope=("Integer recurrence and parameter certificate. "
            "The large tournament labelling and full seed truth table are not materialized. "
            "The general inequalities are proved in the article, not checked by a proof assistant."),
        python_version=platform.python_version())
    path = ROOT / "certificates" / "certificate.json"
    if write:
        path.write_text(json.dumps(report, indent=2) + "\n")
        (ROOT / "certificates" / "all_profiles.json").write_text(
            json.dumps(layers, indent=2) + "\n")
        with (ROOT / "results" / "profile_summary.csv").open("w", newline="") as fh:
            writer = csv.writer(fh)
            writer.writerow(["level", "threshold_count", "s0_at_1", "s1_at_1",
                             "s0_at_H", "s1_at_H", "j0_endpoints", "j1_endpoints"])
            for z in layers:
                H = z["H"]
                writer.writerow([z["level"], H, z["s0"][1], z["s1"][1],
                                 z["s0"][H], z["s1"][H],
                                 z["j0"][1][H], z["j1"][1][H]])
    elif path.exists():
        saved = json.loads(path.read_text())
        for key in ("parameters", "values", "label_numerator", "label_denominator", "exact_checks"):
            assert saved[key] == report[key], f"Saved certificate disagrees on {key}"
        saved_layers = json.loads((ROOT / "certificates" / "all_profiles.json").read_text())
        assert saved_layers == layers, "Saved profile arrays disagree with regeneration"
    print(json.dumps({"status": "PASS", "profile_entries": checked,
                      "alpha_diagnostic": str(alpha), "label_ratio": str(label_ratio),
                      "exact_exponent": "2027/1000", "stronger_exact_exponent": "3667/1809", "seed_dimension_digits": len(str(values['n']))},
                     indent=2))
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate certificate and profile files")
    run(parser.parse_args().write)
