#!/usr/bin/env python3
"""Focused exact checks for the half-parameter Pell proof.

These finite polynomial and auxiliary-block examples corroborate the proof.
They do not instantiate the complete universal system or replace its proof.
No large integer is converted to decimal in the receipt.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
OUT = HERE / "round35_1980_half_parameter_pell_regression.json"


def pell_pair(parameter: int, index: int) -> tuple[int, int]:
    """Compute chi_parameter(index), psi_parameter(index) by binary powering."""
    assert parameter > 1 and index >= 0
    discriminant = parameter * parameter - 1
    result = (1, 0)
    factor = (parameter, 1)
    remaining = index
    while remaining:
        if remaining & 1:
            x, y = result
            z, w = factor
            result = (x * z + discriminant * y * w, x * w + y * z)
        remaining >>= 1
        if remaining:
            z, w = factor
            factor = (z * z + discriminant * w * w, 2 * z * w)
    return result


def check_polynomials(max_half_index: int = 32) -> dict:
    x, t = sp.symbols("X T")
    chi = [sp.Integer(1), x]
    psi = [sp.Integer(0), sp.Integer(1)]
    for index in range(2, 2 * max_half_index + 2):
        chi.append(sp.expand(2 * x * chi[-1] - chi[-2]))
        psi.append(sp.expand(2 * x * psi[-1] - psi[-2]))
    q = [sp.Integer(1), 4 * t - 3]
    for half_index in range(2, max_half_index + 1):
        q.append(sp.expand((4 * t - 2) * q[-1] - q[-2]))
    for half_index in range(max_half_index + 1):
        odd_index = 2 * half_index + 1
        sign = (-1) ** half_index
        assert sp.expand(chi[odd_index] - x * q[half_index].subs(t, x * x)) == 0
        assert sp.expand(q[half_index].subs(t, 1 - x * x) - sign * psi[odd_index]) == 0
        assert q[half_index].subs(t, 0) == sign * odd_index
    return {
        "status": "PASS",
        "odd_indices": list(range(1, 2 * max_half_index + 2, 2)),
        "identities_per_index": 3,
        "identities": [
            "chi_X(2h+1)=X*Q_h(X^2)",
            "Q_h(1-X^2)=(-1)^h*psi_X(2h+1)",
            "Q_h(0)=(-1)^h*(2h+1)",
        ],
        "construction": "chi and psi from their one-step recurrences; Q from its separate two-step recurrence",
    }


def check_modular_constants() -> dict:
    odd_index_cases = 0
    even_index_cases = 0
    for parameter in range(2, 33):
        for index in range(1, 34):
            chi, _ = pell_pair(parameter, index)
            if index % 2:
                assert chi % parameter == 0
                odd_index_cases += 1
            else:
                assert chi % parameter == ((-1) ** (index // 2)) % parameter
                assert chi % parameter != 0
                even_index_cases += 1
    slope_cases = 0
    for modulus in range(2, 33):
        for multiplier in range(1, 4):
            parameter = multiplier * modulus * modulus
            for index in range(1, 34, 2):
                chi, _ = pell_pair(parameter, index)
                quotient, remainder = divmod(chi, parameter)
                assert remainder == 0
                sign = (-1) ** ((index - 1) // 2)
                assert quotient % modulus == (sign * index) % modulus
                slope_cases += 1
    return {
        "status": "PASS",
        "odd_index_divisibility_cases": odd_index_cases,
        "even_index_exclusion_cases": even_index_cases,
        "normalized_root_modulus_cases": slope_cases,
        "parameter_form_for_modulus_cases": "R=i*c^2, c=2..32, i=1..3, odd index 1..33",
    }


def check_positive_construction(parameter: int, index: int = 5) -> dict:
    assert index > 1 and index % 4 == 1
    discriminant = parameter * parameter - 1
    d, c = pell_pair(parameter, index)
    auxiliary_index = 2 * c * index
    f, psi_m = pell_pair(parameter, auxiliary_index)
    old_i, remainder = divmod(psi_m, c * c)
    assert old_i > 0 and remainder == 0
    i = discriminant * old_i
    r_aux = i * c * c
    assert r_aux == discriminant * psi_m
    assert d * d - discriminant * c * c == 1
    assert f * f - discriminant * psi_m * psi_m == 1
    k = r_aux * r_aux
    assert k == discriminant * (f * f - 1)
    chi_r, y_aux = pell_pair(r_aux, index)
    u, remainder = divmod(chi_r, r_aux)
    assert remainder == 0 and u > c > index
    o, remainder_o = divmod(u - c, f)
    j, remainder_j = divmod(u - index, c)
    assert remainder_o == remainder_j == 0
    assert all(value > 0 for value in (d, c, f, i, y_aux, o, j))
    assert u == index + j * c == c + o * f
    assert k * (u * u - y_aux * y_aux) == 1 - y_aux * y_aux
    assert u * u - y_aux * y_aux < 0
    return {
        "status": "PASS",
        "A": parameter,
        "J": index,
        "c": c,
        "m": auxiliary_index,
        "bit_lengths": {"f": f.bit_length(), "R": r_aux.bit_length(),
                        "u": u.bit_length(), "y_aux": y_aux.bit_length()},
        "checks": [
            "main Pell norm", "retained relaxed auxiliary norm", "c^2 divides psi_A(m)",
            "normalized-root divisibility", "both quotient integrality conditions",
            "all auxiliary witnesses positive", "both new congruence equalities",
            "new norm equation", "signed difference negative",
        ],
        "scope": "auxiliary block only; these toy A and J do not assert the full universal system's preliminary bounds",
    }


def check_wrong_parity(parameter: int, index: int = 3) -> dict:
    assert index > 1 and index % 4 == 3
    discriminant = parameter * parameter - 1
    _, c = pell_pair(parameter, index)
    f, psi_m = pell_pair(parameter, 2 * c * index)
    r_aux = discriminant * psi_m
    chi, _ = pell_pair(r_aux, index)
    u, remainder = divmod(chi, r_aux)
    assert remainder == 0
    assert u % f == (-c) % f
    assert u % c == (-index) % c
    assert (u - c) % f != 0
    assert (u - index) % c != 0
    return {
        "status": "PASS negative control",
        "A": parameter,
        "J": index,
        "expected_result": "both proposed positive-quotient congruences fail; signs are negative",
    }


def verify_regression() -> dict:
    return {
        "status": "PASS",
        "polynomials": check_polynomials(),
        "modular_checks": check_modular_constants(),
        "positive_auxiliary_constructions": [check_positive_construction(a) for a in range(2, 6)],
        "wrong_parity_negative_controls": [check_wrong_parity(a) for a in range(2, 6)],
        "proof": "../1980/HALF_PARAMETER_PELL_92_PROOF.md",
        "scope": "finite exact corroboration only; full positive-domain equivalence is proved separately, and the complete 92-operation arithmetic certificate has its own checker",
    }


if __name__ == "__main__":
    receipt = verify_regression()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(receipt["status"], "33 odd polynomial triples; 4 positive auxiliary constructions; 4 parity controls")
    print(receipt["modular_checks"])
    print("Largest positive-example bit lengths:", receipt["positive_auxiliary_constructions"][-1]["bit_lengths"])
