"""Exact arithmetic checks for the report's stable-observable examples.

The checks verify finite instances and implementation contracts.  They do
not claim to prove uniform iPRA derivability or complete Lean proofs.
"""

import json
from copy import deepcopy
from fractions import Fraction as F

from spectral import (matrix, matmul, matsub, frob_sq, jacobi_grid, serialize)
from observables import (psd_certificate, verify_psd_result, root_certificate,
                         verify_root_certificate, projector_certificate,
                         verify_projector_certificate)


def run_checks():
    psd_inputs = [
        [], [[0]], [[2]], [[F(1, 2)]], [[1, 1], [1, 1]],
        [[0, 0], [0, 3]], [[2, 1], [1, 2]],
        [[1, 1, 0], [1, 2, 1], [0, 1, 1]],
        [[0, 0, 0], [0, 2, 1], [0, 1, 2]],
    ]
    negative_inputs = [
        [[-1]], [[0, 1], [1, 0]], [[1, 2], [2, 1]],
        [[0, 0, 1], [0, 2, 0], [1, 0, 0]], [[1, 1], [1, 0]],
    ]
    psd_depths, negative_values = [], []
    for rows in psd_inputs:
        a = matrix(rows)
        result = psd_certificate(a)
        assert result["kind"] == "psd" and verify_psd_result(a, result)
        psd_depths.append(result["elimination_depth"])
    for rows in negative_inputs:
        a = matrix(rows)
        result = psd_certificate(a)
        assert result["kind"] == "negative" and verify_psd_result(a, result)
        negative_values.append(result["negative_value"])

    root_inputs = [
        ([], F(1, 8)), ([[0]], F(1, 8)), ([[2]], F(1, 32)),
        ([[2, 1], [1, 2]], F(1, 8)),
        ([[2, 1], [1, 2]], F(1, 32)),
        ([[1, 1, 0], [1, 2, 1], [0, 1, 1]], F(1, 8)),
        ([[1, 1, 0], [1, 2, 1], [0, 1, 1]], F(1, 32)),
        ([[0, 0], [0, F(1, 2)]], F(1, 32)),
    ]
    roots, root_details = [], []
    for rows, eta in root_inputs:
        a = matrix(rows)
        result = root_certificate(a, eta)
        assert verify_root_certificate(a, result)
        roots.append(result)
        root_details.append({"n": len(a), "eta": eta,
                             "jacobi_steps": result["spectral"]["steps"],
                             "square_grid_denominator": result["denominator"],
                             "residual_verified": True})
    root_stability_cases = 0
    for i, j in [(3, 4), (5, 6), (4, 7)]:
        s, t = roots[i]["S"], roots[j]["S"]
        left = frob_sq(matsub(s, t)) ** 2
        right = len(s) * frob_sq(matsub(matmul(s, s), matmul(t, t)))
        assert left <= right
        root_stability_cases += 1

    weyl_inputs = [
        ([[2, 1], [1, 3]], [[F(17, 8), 1], [1, F(23, 8)]],
         F(1, 4), F(1, 16), F(1, 32)),
        ([[1, 1, 1], [1, 1, 1], [1, 1, 1]],
         [[F(17, 16), 1, 1], [1, F(15, 16), 1], [1, 1, 1]],
         F(1, 8), F(1, 16), F(1, 32)),
        ([[0, 0, 0], [0, 0, 0], [0, 0, 1]],
         [[0, F(1, 64), 0], [F(1, 64), 0, 0], [0, 0, 1]],
         F(1, 32), F(1, 128), F(1, 128)),
    ]
    weyl_coordinates = 0
    for aa, bb, delta, alpha, beta in weyl_inputs:
        a, b = matrix(aa), matrix(bb)
        assert frob_sq(matsub(a, b)) <= delta ** 2
        ca, cb = jacobi_grid(a, alpha), jacobi_grid(b, beta)
        for x, y in zip(ca["d"], cb["d"]):
            assert (x - y) ** 2 <= (delta + alpha + beta) ** 2
            weyl_coordinates += 1

    a = matrix([[2, 1], [1, 3]])
    tau, gamma = F(5, 2), F(3, 4)
    ca, cb = jacobi_grid(a, F(1, 16)), jacobi_grid(a, F(1, 32))
    pa = projector_certificate(a, ca, tau, gamma)
    pb = projector_certificate(a, cb, tau, gamma)
    assert verify_projector_certificate(a, pa)
    assert verify_projector_certificate(a, pb)
    assert pa["rank"] == pb["rank"] == 1
    assert 4 * gamma ** 2 * frob_sq(matsub(pa["P"], pb["P"])) <= (
        ca["epsilon"] + cb["epsilon"]) ** 2
    projector_cases = 2
    for rows, tau, gamma in [
        ([[1, 1, 0], [1, 1, 0], [0, 0, 4]], F(1), F(1, 2)),
        ([[0, 0, 0], [0, 0, 0], [0, 0, 4]], F(2), F(1)),
    ]:
        a = matrix(rows)
        result = projector_certificate(a, jacobi_grid(a, F(1, 32)), tau, gamma)
        assert verify_projector_certificate(a, result)
        projector_cases += 1

    no_gap_a = matrix([[0, 0], [0, 0]])
    no_gap_c = jacobi_grid(no_gap_a, F(1, 8))
    no_gap_p = projector_certificate(no_gap_a, no_gap_c, F(0))
    assert verify_projector_certificate(no_gap_a, no_gap_p)
    projector_cases += 1
    rejections = 0
    for attempt in [
        lambda: projector_certificate(no_gap_a, no_gap_c, F(0), F(1, 4)),
        lambda: root_certificate([[0, 1], [1, 0]], F(1, 8)),
        lambda: root_certificate([[1]], F(0)),
    ]:
        try:
            attempt()
        except ValueError:
            rejections += 1
        else:
            raise AssertionError("An invalid requested contract was accepted")

    corrupted = deepcopy(roots[3])
    corrupted["S"][0][0] += 1
    assert not verify_root_certificate(matrix(root_inputs[3][0]), corrupted)

    return {
        "status": "passed", "psd_certificates": len(psd_inputs),
        "positive_elimination_depths": psd_depths,
        "negative_witnesses": len(negative_inputs), "negative_values": negative_values,
        "root_certificates": root_details, "mixed_basis_root_stability_cases": root_stability_cases,
        "sorted_weyl_matrix_pairs": len(weyl_inputs), "sorted_weyl_coordinates": weyl_coordinates,
        "projector_certificates": projector_cases, "projector_cross_precision_stability_cases": 1,
        "invalid_contract_rejections": rejections, "corrupted_root_certificate_rejections": 1,
        "qualification": "Finite exact arithmetic checks; not a uniform iPRA or Lean proof.",
    }


if __name__ == "__main__":
    print(json.dumps(serialize(run_checks()), indent=2))
