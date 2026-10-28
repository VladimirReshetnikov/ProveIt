"""Exact packing-gate certificates for the two proposed recursive schedules.

This checker validates the rational prefix parameters and exact integer-power
upper bounds on their logarithms. It does not certify local aggregation
coefficients or independently prove the imported contraction interface.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def encode(value: F) -> dict:
    return {"numerator": value.numerator, "denominator": value.denominator,
            "decimal_illustration": float(value)}


LOG_UPPER = {
    4: F(2),
    6: F(517, 200),
    7: F(14037, 5000),
    10: F(1661, 500),
    13: F(7401, 2000),
    15: F(3907, 1000),
}


def audit(name: str, alphabets: list[int], etas: list[F], delta: F, capacity: F) -> dict:
    cumulative = F(0)
    mass = F(1)
    rows = []
    for depth, (r, eta) in enumerate(zip(alphabets, etas)):
        previous = cumulative
        cumulative += eta
        retained = delta if depth == 0 else max(delta, previous)
        fresh = delta if depth == 0 else previous
        A_log_r = cumulative * LOG_UPPER[r]
        exponents = {
            "QR_over_M": retained + A_log_r,
            "Q_squared_C_over_M": fresh + 2 * A_log_r,
            "L_Q_squared_over_M": cumulative + 2 * A_log_r,
        }
        for gate, exponent in exponents.items():
            require(exponent < 1, f"{name}, depth {depth}: failed {gate}")
        rows.append({
            "depth": depth, "alphabet": r, "eta": encode(eta),
            "cumulative_eta": encode(cumulative), "wire_mass_coefficient": encode(mass),
            "degree_exponents": {"retained": encode(retained), "fresh": encode(fresh)},
            "gate_exponent_upper_bounds": {key: encode(value) for key, value in exponents.items()},
            "strict_gaps_below_one": {key: encode(1 - value) for key, value in exponents.items()},
        })
        mass *= F(2, r)
    remaining = capacity - cumulative
    require(remaining > 0, f"{name}: no positive tail budget")
    q = F(63, 100)
    contraction_upper = F(11, 20)
    require(q > contraction_upper, "tail taper vanishes too quickly for the depth bootstrap")
    tail_exponents = {
        "QR_over_M": max(delta, capacity) + 2 * capacity,
        "Q_squared_C_over_M": 5 * capacity,
        "L_Q_squared_over_M": 5 * capacity,
    }
    require(all(value <= 1 for value in tail_exponents.values()),
            f"{name}: tail packing exponent exceeds one")
    retreat = {}
    for gate, exponent in tail_exponents.items():
        if exponent == 1:
            if gate == "QR_over_M":
                # Here delta is the dominant retained degree; only 2A scales
                # with Lambda=lambda-ceil(sqrt(lambda)).
                require(delta > capacity, "unexpected boundary case")
                retreat[gate] = encode(2 * capacity)
            else:
                retreat[gate] = encode(5 * capacity)
    return {
        "name": name, "root_degree_exponent": encode(delta),
        "total_capacity": encode(capacity), "prefix": rows,
        "tail": {
            "alphabet": 4, "ratio_q": encode(q),
            "allowed_child_ratio": encode(contraction_upper),
            "remaining_capacity": encode(remaining),
            "first_eta": encode((1 - q) * remaining),
            "first_wire_mass_coefficient": encode(mass),
            "limiting_gate_exponents": {key: encode(value) for key, value in tail_exponents.items()},
            "boundary_retreat_coefficients_on_sqrt_lambda": retreat,
            "minimum_taper_positive_power_illustration": 1 + math.log(float(q)) / math.log(F(20, 11)),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    logs = []
    for r, upper in LOG_UPPER.items():
        left = r ** upper.denominator
        right = 1 << upper.numerator
        if r == 4:
            require(left == right, "incorrect exact logarithm of four")
        else:
            require(left < right, f"incorrect strict upper bound on log_2({r})")
        logs.append({"alphabet": r, "log2_upper": encode(upper),
                     "integer_power_check": "equal" if left == right else "strictly_less"})
    result = {
        "status": "passed", "logarithm_certificates": logs,
        "schedules": [
            audit("generic", [10, 13, 10, 7],
                  [F(301, 20000), F(287, 25000), F(357, 100000), F(193, 50000)],
                  F(9, 10), F(1, 20)),
            audit("low_degree", [15, 10, 7, 6],
                  [F(2149, 20000), F(2337, 100000), F(407, 20000), F(109, 10000)],
                  F(1, 12), F(1, 5)),
        ],
        "scope": "Exact prefix packing gates and tail capacity/depth conditions; local backend beta values and headline runtime coefficients are outside this check.",
    }
    rendered = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
