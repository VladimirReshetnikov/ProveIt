#!/usr/bin/env python3
"""Deterministic exact tests; executable verification, not formal proof."""

from fractions import Fraction
from itertools import product
import json

from rotation_certificates import (
    IDENTITY, ZERO, axis_certificate, certificate_json, cross_matrix,
    determinant, dot, is_rotation, matrix, matvec,
    finite_rotation_approximation, normalized_approximation,
    polynomial_rodrigues, quaternion_rotation, rodrigues_matrix,
    verify_certificate,
)


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def check_matrix(r):
    require(is_rotation(r), "quaternion formula must give SO(3)")
    cert = axis_certificate(r)
    require(verify_certificate(r, cert), "axis/Rodrigues certificate")
    require(rodrigues_matrix(cert) == r, "exact matrix reconstruction")
    require(matvec(r, cert.v) == cert.v, "fixed axis")
    require(cert.q == dot(cert.v, cert.v) and cert.q > 0, "axis nonzero")
    require(cert.c*cert.c + cert.b*cert.b/cert.q == 1, "unit circle")
    require(matvec(cross_matrix(cert.v), cert.v) == ZERO, "cross kills axis")
    for bits in (0, 8, 32):
        appr = normalized_approximation(cert, bits)
        require(appr.root_lower*appr.root_lower <= cert.q
                < appr.root_upper*appr.root_upper, "square root bracket")
        require(appr.error_bound < Fraction(1, 1 << bits), "coordinate error bound")
        require(appr.u == tuple(x/appr.root_lower for x in cert.v), "axis approximants")
        require(appr.s == cert.b/appr.root_lower, "sine approximant")
    return cert


def check_finite_approximation(r, bits):
    result = finite_rotation_approximation(r, bits)
    epsilon = result.epsilon
    eta = epsilon/32
    d = (3-sum((r[i][i] for i in range(3)), Fraction(0)))/2
    require(abs(result.d_sample-d) <= epsilon*epsilon/32, "branch sample error")
    p = polynomial_rodrigues(result.U, result.C, result.V)
    residual = tuple(x-y for x, y in zip(matvec(r, result.U), result.U))
    entry_error = max(abs(p[i][j]-r[i][j]) for i in range(3) for j in range(3))
    if result.near_identity:
        frobenius_squared = sum(((r[i][j]-IDENTITY[i][j])**2
                                 for i in range(3) for j in range(3)), Fraction(0))
        require(result.d_sample <= epsilon*epsilon/8, "near branch threshold")
        require(d <= 5*epsilon*epsilon/32, "near branch trace bound")
        require(frobenius_squared == 4*d <= 5*epsilon*epsilon/8,
                "near branch Frobenius bound")
        require(dot(residual, residual) <= epsilon*epsilon, "near residual norm")
        require(result.U == (1, 0, 0) and result.C == 1 and result.V == 0,
                "near branch exact finite output")
    else:
        require(result.d_sample > epsilon*epsilon/8, "far branch threshold")
        require(d > 3*epsilon*epsilon/32 >= epsilon*epsilon/16,
                "far branch supplied gap")
        require(verify_certificate(r, result.cert), "far branch exact certificate")
        require(result.coordinate_error_bound < eta, "far coordinate samples")
        require(abs(dot(result.U, result.U)-1) <= 9*eta, "finite axis normalization")
        require(abs(result.C*result.C+result.V*result.V-1) <= 6*eta,
                "finite circle normalization")
        require(max(abs(x) for x in residual) <= 4*eta, "finite fixed-axis residual")
        require(entry_error <= 14*eta, "finite Rodrigues reconstruction")
    require(entry_error <= epsilon, "final finite reconstruction tolerance")
    return result.near_identity


def main():
    grid_count = 0
    grid_identity_count = 0
    grid_half_turn_count = 0
    for quat in product(range(-2, 3), repeat=4):
        if quat == (0, 0, 0, 0):
            continue
        cert = check_matrix(quaternion_rotation(*quat))
        grid_count += 1
        grid_identity_count += int(cert.identity_case)
        grid_half_turn_count += int(cert.c == -1)

    edge_count = 0
    for bits in (1, 8, 32, 128):
        large = 1 << bits
        for quat in ((large, 1, 0, 0), (large, 0, -1, 0),
                     (large, 0, 0, 1), (large, 1, 2, -3),
                     (1, large, 0, 0), (1, 0, -large, 0),
                     (1, 0, 0, large)):
            check_matrix(quaternion_rotation(*quat))
            edge_count += 1
    for quat in ((0, 2, -3, 5), (0, 1, 1, 1),
                 (Fraction(1, 7), Fraction(2, 9), Fraction(-3, 11), Fraction(5, 13))):
        check_matrix(quaternion_rotation(*quat))
        edge_count += 1

    rejected = 0
    for bad in (matrix(((-1, 0, 0), (0, 1, 0), (0, 0, 1))),
                matrix(((2, 0, 0), (0, 2, 0), (0, 0, 2))),
                matrix(((0, 0, 0), (0, 0, 0), (0, 0, 0)))):
        try:
            axis_certificate(bad)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("invalid matrix was accepted")

    quarter_turn = quaternion_rotation(1, 0, 0, 1)
    require(quarter_turn == matrix(((0, -1, 0), (1, 0, 0), (0, 0, 1))),
            "right-hand cross-product orientation")
    require(axis_certificate(IDENTITY).identity_case, "identity branch")
    require(determinant(quarter_turn) == 1, "determinant orientation")

    finite_near_count = 0
    finite_far_count = 0
    for bits in (0, 4, 12):
        cases = ((1, 0, 0, 0), (0, 2, -3, 5),
                 (1 << (bits+1), 1, 0, 0),
                 (1 << (bits+2), 1, 0, 0),
                 (1 << (bits+3), 1, 0, 0),
                 (1 << (bits+2), 1, 1, 1),
                 (1 << (bits+4), 1, 1, 1))
        for quat in cases:
            near = check_finite_approximation(quaternion_rotation(*quat), bits)
            finite_near_count += int(near)
            finite_far_count += int(not near)
    require(finite_near_count > 0 and finite_far_count > 0, "both finite branches exercised")

    print(json.dumps({
        "status": "passed",
        "verification_kind": "executable exact rational arithmetic; not a formal proof",
        "integer_quaternion_grid": {"coordinate_range": [-2, 2],
                                    "nonzero_quaternions": grid_count,
                                    "identity_cases": grid_identity_count,
                                    "half_turn_cases": grid_half_turn_count},
        "additional_edge_cases": edge_count,
        "largest_small_angle_scale": "2^128",
        "normalization_precisions_bits": [0, 8, 32],
        "normalization_checks": 3*(grid_count+edge_count),
        "invalid_inputs_rejected": rejected,
        "finite_precision_branch_checks": {
            "precisions_bits": [0, 4, 12],
            "near_identity": finite_near_count,
            "far_from_identity": finite_far_count,
            "finite_U_C_V_bounds_checked": ["9 eta", "6 eta", "4 eta", "14 eta"],
        },
        "quarter_turn_certificate": certificate_json(axis_certificate(quarter_turn)),
        "half_turn_certificate": certificate_json(axis_certificate(quaternion_rotation(0, 2, -3, 5))),
    }, indent=2))


if __name__ == "__main__":
    main()
