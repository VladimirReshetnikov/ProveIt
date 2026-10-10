#!/usr/bin/env python3
"""Quick consolidated exact-only replay of the analytic specialization certificates.

This checker evaluates no numerical integrals and does not rerun the
separate distribution-matrix audit. It checks the five source Gaussian
identities, the three additional displayed Gaussian examples, six cases
of the general Gaussian edge family, 16 bilateral partial fractions, ten
displayed mixed-root identities, and the weight-five shuffle certificate.

    python code/verify_exact.py
    python code/verify_exact.py --output results/exact_replay_summary.json

Dependencies: Python >=3.10, SymPy >=1.12, and the local package modules.
mpmath is imported by the mixed modules but no numerical routine is called.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp

from gaussian_parity import beta, zeta, gaussian_component, verify_weight_six
from mixed_parity import partial_fraction_symbolic, height_one_exact
from verify_mixed import explicit_identities
from verify_weight5 import exact_replay as weightfive_exact_replay


def displayed_gaussian_identities():
    """Independent transcription of article equations g71, g91, and g53."""
    p = sp.pi
    return {
        (7, 1): 3*beta(8)-5*p**5*zeta(3)/1536-p**3*zeta(5)/32
                -8255*p*zeta(7)/32768,
        (9, 1): 4*beta(10)-61*p**7*zeta(3)/184320-5*p**5*zeta(5)/1536
                -p**3*zeta(7)/32-131327*p*zeta(9)/524288,
        (5, 3): 17*beta(8)+5*p**2*beta(6)/48-3087*p**3*zeta(5)/16384
                -123825*p*zeta(7)/32768,
    }


def edge_family(m):
    """Independent transcription of the article's all-orders edge formula."""
    if not isinstance(m, int) or m < 2:
        raise ValueError("The stated edge family has integer m >= 2")
    two = sp.Integer(2)
    answer = (m-1)*beta(2*m)
    answer -= sp.pi/4*(1+two**(1-2*m)-two**(3-4*m))*zeta(2*m-1)
    answer -= sum(abs(sp.euler(2*j))*sp.pi**(2*j+1)*zeta(2*m-2*j-1)
                  /(two**(2*j+2)*sp.factorial(2*j)) for j in range(1, m-1))
    return sp.expand(answer)


def run_exact_checks():
    source_gaussian = verify_weight_six()

    extra_gaussian = []
    for (a, b), rhs in displayed_gaussian_identities().items():
        difference = sp.expand(gaussian_component(a, b)-rhs)
        assert difference == 0, ("displayed Gaussian", a, b, difference)
        extra_gaussian.append({"a": a, "b": b, "transcribed_rhs": str(rhs),
                               "exact_difference": "0"})

    edges = []
    for m in range(2, 8):
        rhs = edge_family(m)
        difference = sp.expand(gaussian_component(2*m-1, 1)-rhs)
        assert difference == 0, ("Gaussian edge", m, difference)
        edges.append({"m": m, "a": 2*m-1, "b": 1, "exact_difference": "0"})

    n, h = sp.symbols("n h", nonzero=True)
    partial_fractions = []
    for a in range(2, 6):
        for b in range(1, 5):
            lhs = 1/(n**b*(n-h)**a)
            difference = sp.cancel(lhs-partial_fraction_symbolic(a, b, n, h))
            assert difference == 0, ("partial fraction", a, b, difference)
            partial_fractions.append({"a": a, "b": b, "exact_difference": "0"})

    mixed = []
    for (a, level), rhs in explicit_identities().items():
        difference = sp.simplify(height_one_exact(a, level)-rhs)
        assert difference == 0, ("displayed mixed", a, level, difference)
        mixed.append({"a": a, "level": level, "transcribed_rhs": str(rhs),
                      "exact_difference": "0"})

    weightfive = weightfive_exact_replay()
    counts = {
        "source_gaussian_identities": source_gaussian["identities"],
        "additional_displayed_gaussian_identities": len(extra_gaussian),
        "gaussian_edge_family_cases": len(edges),
        "mixed_partial_fraction_identities": len(partial_fractions),
        "displayed_mixed_identities": len(mixed),
        "weight_five_shuffle_rows": 2,
        "weight_five_labelled_interleavings": sum(
            weightfive[name]["labelled_interleavings"]
            for name in ("first_shuffle", "second_shuffle")),
        "weight_five_linear_combinations": 1,
    }
    return {
        "status": "all exact checks passed",
        "method": "Exact rational and symbolic arithmetic; independent displayed-formula transcriptions",
        "numerical_evaluations_performed": 0,
        "distribution_matrix_runs_performed": 0,
        "counts": counts,
        "source_gaussian": source_gaussian,
        "additional_displayed_gaussian": extra_gaussian,
        "gaussian_edge_family": edges,
        "mixed_partial_fractions": partial_fractions,
        "displayed_mixed": mixed,
        "weight_five": {
            "status": weightfive["exact_replay_status"],
            "certificate_multipliers": weightfive["certificate_multipliers"],
            "double_coefficients": weightfive["final_double_coefficients"],
            "constant_coefficients": weightfive["final_constant_coefficients"],
            "original_certificate_comparison": weightfive["original_certificate_comparison"],
            "full_certificate": "results/weight5_replay.json",
        },
        "scope_note": "Finite exact replays audit specializations and implementation; the article supplies the all-orders proofs.",
    }


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=root/"results"/"exact_replay_summary.json")
    args = parser.parse_args()
    results = run_exact_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": results["status"], "counts": results["counts"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
