#!/usr/bin/env python3
"""Compact layer/carry report built on cascade_experiments.py."""

import importlib.util
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "ce", Path(__file__).with_name("cascade_experiments.py")
)
ce = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ce)


def report(T, M, A):
    data = ce.block_data(T, M, A)
    out = {"T": T, "M": M, "A": A, "N": data["N"]}
    for p in (2, 3):
        weights = [x[0 if p == 2 else 1] for x in data["pairs"]]
        tau = ce.tropical_min(data["n"], weights)
        actual, _ = ce.exact_det_valuation(data, p, tau)
        excess = actual - tau
        precision = excess + 16
        coeffs = ce.layer_coefficients(data, p, excess + 6, precision)
        layers = []
        total = 0
        modulus = p ** precision
        for delta, coeff in coeffs.items():
            vc = ce.v_p(coeff, p, precision)
            effective = delta + vc
            if effective <= excess + 6:
                layers.append({"delta": delta, "vp_coeff": vc, "effective": effective})
            total = (total + coeff * pow(p, delta, modulus)) % modulus
        out[f"p{p}"] = {
            "tau": tau,
            "excess": excess,
            "initial": ce.first_fiber_valuation(data, p),
            "gap": ce.first_assignment_gap(data["n"], weights),
            "vp_reconstructed_sum": ce.v_p(total, p, precision),
            "layers_near_final": layers,
            "number_of_supported_deltas": len(coeffs),
            "max_delta": max(coeffs),
        }
    return out


if __name__ == "__main__":
    T, M, A = map(int, sys.argv[1:])
    print(json.dumps(report(T, M, A), sort_keys=True))
