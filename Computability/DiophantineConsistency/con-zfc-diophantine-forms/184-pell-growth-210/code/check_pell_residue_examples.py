#!/usr/bin/env python3
"""Reproduce eight examples of the standalone Pell residue construction.

These are modular checks of an auxiliary lemma. They are NOT solutions of the
full Diophantine consistency equation, and they do not prove Con(ZFC), its
negation, or the unbounded lemma by testing examples. The proof of that lemma
is in growth_proof.md. All arithmetic here uses only the Python standard
library; the enormous full Pell integers are not constructed.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

DILATION = 1 << 19
PARAMETERS = (1, 2, 3, 7, 16, 31, 100, 1000)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def pell_mod(base: int, index: int, modulus: int) -> tuple[int, int]:
    """Return (X_index(base), Y_index(base)) modulo modulus by binary powering."""
    require(type(base) is int and index >= 0 and modulus > 0, "invalid Pell input")
    discriminant = (base * base - 1) % modulus

    def multiply(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        x, y = left
        u, v = right
        return ((x * u + discriminant * y * v) % modulus,
                (x * v + y * u) % modulus)

    result = (1 % modulus, 0)
    power = (base % modulus, 1 % modulus)
    remaining = index
    while remaining:
        if remaining & 1:
            result = multiply(result, power)
        power = multiply(power, power)
        remaining //= 2
    return result


def invert_ordinate(base_residue: int, target: int, bits: int) -> tuple[int, int]:
    """Lift the unique index residue for Y_s(base)=target modulo 2**bits."""
    modulus = 1 << bits
    require(bits >= 2 and base_residue % 4 == 1, "invalid inverse-lemma input")
    target %= modulus
    require(target % 2 == 1, "an odd target is required")
    index = target & 1
    changes = 0
    for lower_bits in range(1, bits):
        current_modulus = 1 << (lower_bits + 1)
        _, ordinate = pell_mod(base_residue, index, current_modulus)
        if ordinate != target % current_modulus:
            index += 1 << lower_bits
            changes += 1
        require(pell_mod(base_residue, index, current_modulus)[1]
                == target % current_modulus, "bit lift failed")
    require(index > 0 and index % 2 == 1, "lifted index is not positive odd")
    require(pell_mod(base_residue, index, modulus)[1] == target,
            "completed inverse failed")
    return index, changes


def check_example(parameter: int) -> dict[str, int | bool]:
    horizon_parameter = (1 << 12) * parameter
    horizon = 16 + 4 * horizon_parameter * horizon_parameter
    require(horizon % (1 << 26) == 16, "cofinal horizon congruence failed")
    base = 4 * horizon + 1
    initial_index = DILATION * horizon
    precision_bits = horizon.bit_length() + 9
    inverse_bits = precision_bits - 23
    modulus = 1 << precision_bits
    inverse_modulus = 1 << inverse_bits

    initial_trace, initial_ordinate = pell_mod(base, initial_index, modulus)
    require(initial_ordinate % (1 << 23) == 0, "ordinate is not divisible by 2**23")
    normalized_ordinate = initial_ordinate >> 23
    require(normalized_ordinate % 2 == 1, "ordinate has the wrong exact valuation")
    odd_horizon_part = horizon // 16

    # This computes y0/(d*t) modulo 2**inverse_bits. Only the power-of-two
    # factor is divided as an ordinary integer; the odd factor is inverted.
    normalizer = (normalized_ordinate
                  * pow(odd_horizon_part, -1, inverse_modulus)) % inverse_modulus
    target = pow((odd_horizon_part * normalizer) % inverse_modulus,
                 -1, inverse_modulus)
    normalized_base = initial_trace % inverse_modulus
    odd_multiplier, changed_bits = invert_ordinate(normalized_base, target, inverse_bits)

    final_index = initial_index * odd_multiplier
    final_trace, final_ordinate = pell_mod(base, final_index, modulus)
    require(final_ordinate == 1 << 23, "target Pell residue was not attained")
    require(horizon < modulus, "precision does not exceed the horizon")
    require((final_ordinate & horizon) == 0, "the binary supports intersect")
    require((final_trace * final_trace
             - (base * base - 1) * final_ordinate * final_ordinate - 1) % modulus == 0,
            "modular Pell norm failed")

    return {
        "cofinal_parameter": parameter,
        "horizon_parameter": horizon_parameter,
        "t": horizon,
        "pell_base": base,
        "initial_index": initial_index,
        "precision_bits": precision_bits,
        "inverse_precision_bits": inverse_bits,
        "normalizer_modulus_residue": normalizer,
        "target_ordinate_modulus_residue": target,
        "chosen_odd_multiplier": odd_multiplier,
        "changed_lift_bits": changed_bits,
        "final_index": final_index,
        "final_ordinate_residue": final_ordinate,
        "expected_residue": 1 << 23,
        "binary_supports_disjoint": True,
        "modular_pell_norm_checked": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, help="also save the deterministic JSON receipt")
    args = parser.parse_args()
    receipt = {
        "status": "PASS",
        "scope": ("Eight modular examples of the standalone Pell residue construction. "
                  "These are not zeros of the full Diophantine consistency polynomial. "
                  "They do not prove consistency, inconsistency, or the unbounded theorem."),
        "full_pell_integers_constructed": False,
        "dilation": DILATION,
        "cofinal_horizon_formula": "z=2^12*k; t=16+4*z^2",
        "target_residue_formula": "Y_n(4*t+1)=2^23 modulo 2^L",
        "binomial_parity_reason": ("The checked residue has binary support disjoint from t, "
                                   "and t<2^L; therefore the full Pell ordinate F and t "
                                   "have no overlapping binary bits. The proof's parity "
                                   "criterion then makes binom(F+t,t) odd."),
        "examples": [check_example(k) for k in PARAMETERS],
    }
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt is not None:
        args.receipt.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
