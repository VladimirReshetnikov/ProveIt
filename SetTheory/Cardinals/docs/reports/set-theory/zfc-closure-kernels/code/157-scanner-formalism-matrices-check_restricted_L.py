#!/usr/bin/env python3
"""Independent exhaustive checks of two three-valued native-code matrices.

This is a finite logical-fragment obstruction, not a countermodel of the
full calculus: the gated set-theoretic bundle is deliberately excluded.
Only the Python standard library is used. There is no search in this file.
"""
from itertools import product
from math import isqrt
import hashlib
import json
from pathlib import Path


MATRICES = {
    "U_equals_A": {
        "implication": [[0, 1, 2], [0, 0, 0], [0, 2, 0]],
        "quantifier": [0, 1, 1],
        "membership": 1,
        "equality": 2,
        "restrictions": ["A"],
        "counterexample": {"schema": "S", "native_parameters": [3, 3, 1]},
    },
    "U_in_B_C_0_1": {
        "implication": [[0, 2, 2], [0, 0, 1], [0, 0, 0]],
        "quantifier": [0, 1, 2],
        "membership": 1,
        "equality": 0,
        "restrictions": ["B", "C", "0", "1"],
        "counterexample": {"schema": "K", "native_parameters": [1, 0]},
    },
}


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def check_matrix(name, m):
    carrier = range(3)
    I = lambda a, b: m["implication"][a][b]
    Q = lambda i, a: m["quantifier"][a]
    R = lambda a, b: m["membership"]
    E = lambda a, b: m["equality"]
    N = lambda a: I(a, 1)
    Ex = lambda i, a: N(Q(i, N(a)))
    designated = lambda a: a == 0
    schema = {
        "rho1": lambda a, b, c: Ex(a, E(a, b)),
        "rho2": lambda a, b, c: I(Q(a, I(b, c)), I(Q(a, b), Q(a, c))),
        "rho3": lambda a, b, c: I(E(a, b), I(R(c, a), R(c, b))),
        "rho4": lambda a, b, c: I(Q(a, Q(b, c)), Q(b, Q(a, c))),
        "rho5": lambda a, b, c: I(E(c, a), I(R(c, b), R(a, b))),
        "rho6": lambda a, b, c: I(Ex(a, Q(a, b)), b),
        "G": lambda a, b, c: I(E(c, a), I(E(c, b), Q(R(a, b), E(a, b)))),
    }
    L = lambda a, b, c, u: I(I(I(c, u), a), I(I(a, c), I(b, c)))
    K = lambda a, b: I(a, I(b, a))
    S = lambda a, b, c: I(I(a, I(b, c)), I(I(a, b), I(a, c)))

    # Truth, the literal code alias I(0,0)=0, MP, and closed GEN.
    assert I(0, 0) == 0
    assert all(not (designated(a) and designated(I(a, b))) or designated(b)
               for a, b in product(carrier, repeat=2))
    assert all(not designated(a) or designated(Q(i, a))
               for i, a in product(carrier, repeat=2))
    for row, f in schema.items():
        assert all(designated(f(*v)) for v in product(carrier, repeat=3)), row
    for restriction in m["restrictions"]:
        for a, b, c in product(carrier, repeat=3):
            u = {"A": a, "B": b, "C": c, "0": 0, "1": 1}[restriction]
            assert designated(L(a, b, c, u)), (restriction, a, b, c)

    def native_value(n):
        assert type(n) is int and n >= 0
        if n == 0:
            return 0
        a, b = unpair(n // 4)
        # This is a well-founded valuation on all naturals, not just formulas
        # accepted by a syntactic parser. The only self-reference was code zero.
        assert a < n and b < n
        va, vb = native_value(a), native_value(b)
        return (I, R, Q, E)[n % 4](va, vb)

    assert native_value(1) == 1  # F = R(0,0), so falsum is undesignated.
    native_witnesses = [0, 1, 3] if name == "U_equals_A" else [0, 1, 8]
    assert set(map(native_value, native_witnesses)) == set(carrier)
    witness = m["counterexample"]
    values = list(map(native_value, witness["native_parameters"]))
    value = {"K": K, "S": S}[witness["schema"]](*values)
    assert not designated(value)

    # Extra rows that the U=A matrix also validates. Their inclusion alone
    # therefore cannot repair the S obstruction.
    extra = {
        "identity": lambda a, b, c: I(a, a),
        "K": lambda a, b, c: K(a, b),
        "explosion": lambda a, b, c: I(1, a),
        "double_negation_elimination": lambda a, b, c: I(N(N(a)), a),
        "quantifier_stability": lambda a, b, c: I(N(N(Q(a, b))), Q(a, b)),
    }
    valid_extra = [row for row, f in extra.items()
                   if all(designated(f(*v)) for v in product(carrier, repeat=3))]

    # The exact helper-free bundle, factored from Codes222.v. Evaluate one
    # permitted native instance to check that our exclusion is substantive.
    def bundle(a, b, c):
        t = Q(b, I(c, I(Q(b, I(c, I(R(b, c), 1))), 1)))
        alpha = Q(a, I(Q(c, I(R(c, a), R(c, b))), t))
        beta = Q(a, I(c, I(alpha, 1)))
        gamma = Q(b, I(R(b, c), I(beta, 1)))
        nks = Q(c, I(gamma, I(t, 1)))
        vrel = I(R(a, b), Q(c, R(a, b)))
        return N(I(vrel, nks))

    bundle_codes = [1, 3, 0]
    assert bundle_codes[2] not in bundle_codes[:2]  # Gate c != a,b holds.
    bundle_value = bundle(*map(native_value, bundle_codes))
    assert not designated(bundle_value)
    return {
        "status": "PASS",
        "name": name,
        "matrix": m,
        "designated": [0],
        "logical_rows_checked": list(schema),
        "checks_per_row": 27,
        "inference_rules_checked": ["truth", "modus_ponens", "closed_GEN"],
        "native_alias_I00": 0,
        "native_attainability_witnesses": native_witnesses,
        "counterexample_values": values,
        "counterexample_value": value,
        "additional_valid_rows": valid_extra,
        "excluded_gated_bundle_counterexample": {
            "native_parameters": bundle_codes, "value": bundle_value,
        },
        "scope": "Logical fragment only. No countermodel of the full gated-bundle calculus; its equiconsistency is unresolved here.",
    }


def main():
    result = {
        "status": "PASS",
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "matrices": [check_matrix(name, m) for name, m in MATRICES.items()],
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
