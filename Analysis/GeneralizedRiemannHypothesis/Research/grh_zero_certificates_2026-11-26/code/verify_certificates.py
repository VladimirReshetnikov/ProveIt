#!/usr/bin/env python3
"""Exact certificates and high-precision illustrations for Hankel root detection.

For a conjugation-invariant multiset of n roots in the closed unit disk, write
    s_k = sum(z**k), H[i,j] = s_(i+j), b = max(abs(Im z)),
    D = max(0, -lambda_min(H)), m = floor(n/2).
The accompanying paper proves, for n >= 2,
    2*(b/(4*m))**(2*n-2) <= D <= C_n*b**2,
    C_n = n**2*(n-1)*(7*n-11)/6.

This script checks exact examples, algebraic identities, interpolation witnesses,
and rational positive-semidefinite certificates. It does not replace the paper's
general proof and is not a Lean formalization. Eigenvalues are illustrations,
computed with mpmath; all certificates use exact SymPy rational arithmetic.

Run: python3 code/verify_certificates.py
Dependencies: Python 3, sympy, mpmath. No network access is used.
"""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import json
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp


I = sp.I


def require(condition, message):
    """Do not let Python's -O option disable verification."""
    if not bool(condition):
        raise AssertionError(message)


def exact(z):
    return sp.cancel(sp.expand(z))


def rational_complex(z):
    z = sp.sympify(z)
    a, b = z.as_real_imag()
    a, b = sp.simplify(a), sp.simplify(b)
    require(a.is_Rational and b.is_Rational,
            "The finite examples require exact rational real/imaginary parts.")
    return a + I*b


def abs_squared(z):
    z = rational_complex(z)
    return exact(sp.re(z)**2 + sp.im(z)**2)


def matrix_strings(matrix):
    return [[str(v) for v in row] for row in matrix.tolist()]


def same_matrix(left, right):
    return left.shape == right.shape and all(
        exact(a-b) == 0 for a, b in zip(left, right))


def validate_roots(roots):
    roots = [rational_complex(z) for z in roots]
    require(len(roots) >= 2, "At least two roots are needed.")
    require(Counter(roots) == Counter([sp.conjugate(z) for z in roots]),
            "Root multiset is not invariant under conjugation.")
    require(all(abs_squared(z) <= 1 for z in roots),
            "All example roots must lie in the closed unit disk.")
    return roots


def hankel_from_roots(roots):
    roots = validate_roots(roots)
    n = len(roots)
    moments = [exact(sum(z**k for z in roots)) for k in range(2*n-1)]
    require(all(s.is_Rational for s in moments), "Moments must be rational.")
    return moments, sp.Matrix(n, n, lambda i, j: moments[i+j])


def rational_psd(matrix):
    """Decide PSD by rational symmetric Schur elimination.

    A positive pivot is eliminated by a rational congruence. A zero diagonal
    pivot is allowed only when the remaining row is zero. If that row has a
    nonzero entry, an explicit two-coordinate vector gives a negative form.
    The accumulated congruence transfers this vector to the original matrix.
    A PSD answer includes T with T^T A T diagonal and nonnegative; a non-PSD
    answer includes an exact rational vector v with v^T A v < 0.
    """
    a = sp.Matrix(matrix)
    require(a.rows == a.cols and a == a.T, "PSD input must be symmetric.")
    require(all(x.is_Rational for x in a), "PSD input must be rational.")
    n = a.rows
    b, transform = a.copy(), sp.eye(n)
    steps = []
    for k in range(n):
        pivot = b[k, k]
        if pivot < 0:
            vector = transform[:, k]
            value = exact((vector.T*a*vector)[0])
            require(value < 0, "Negative-pivot witness failed.")
            return {
                "is_psd": False, "reason": "negative Schur pivot",
                "pivot_index": k, "pivot": str(pivot), "steps": steps,
                "witness": [str(x) for x in vector],
                "quadratic_value": str(value),
            }
        if pivot == 0:
            j = next((j for j in range(k+1, n) if b[k, j] != 0), None)
            if j is not None:
                # For s != 0 and d real, t=-s/(|d|+1) gives 2st+dt^2<0.
                s, d = b[k, j], b[j, j]
                t = -s/(abs(d)+1)
                local_vector = sp.zeros(n, 1)
                local_vector[k], local_vector[j] = 1, t
                vector = transform*local_vector
                value = exact((vector.T*a*vector)[0])
                require(value < 0, "Zero-pivot off-diagonal witness failed.")
                return {
                    "is_psd": False,
                    "reason": "zero diagonal with nonzero remaining row",
                    "pivot_index": k, "off_diagonal_index": j,
                    "steps": steps, "witness": [str(x) for x in vector],
                    "quadratic_value": str(value),
                }
            steps.append({"index": k, "pivot": "0", "action": "zero row"})
            continue
        change = sp.eye(n)
        for j in range(k+1, n):
            change[k, j] = -b[k, j]/pivot
        b = (change.T*b*change).applyfunc(exact)
        transform = (transform*change).applyfunc(exact)
        steps.append({"index": k, "pivot": str(pivot),
                      "action": "positive Schur pivot"})
    require(same_matrix(transform.T*a*transform, b), "Congruence identity failed.")
    require(b == sp.diag(*[b[i, i] for i in range(n)]), "Final form not diagonal.")
    require(all(b[i, i] >= 0 for i in range(n)), "Negative diagonal remains.")
    require(transform.det() == 1, "Congruence transformation is not invertible.")
    return {
        "is_psd": True, "steps": steps,
        "congruence_transform": matrix_strings(transform),
        "diagonal": [str(b[i, i]) for i in range(n)],
        "transform_determinant": "1",
    }


def cluster_interpolation_certificate(name, roots):
    """Construct the i/-i/0 polynomial using a largest imaginary-height gap."""
    roots = validate_roots(roots)
    n, m = len(roots), len(roots)//2
    heights = sorted({sp.im(z) for z in roots if sp.im(z) > 0})
    require(bool(heights), "This certificate requires a nonreal root.")
    b = heights[-1]
    endpoints = list(zip([sp.Integer(0)] + heights[:-1], heights))
    lower, upper = max(endpoints, key=lambda pair: pair[1]-pair[0])
    gap = upper-lower
    require(gap >= b/m, "Largest-gap lower bound failed.")
    nodes = sorted(set(roots), key=lambda z: (sp.im(z), sp.re(z)))
    values = [I if sp.im(z) >= upper else
              -I if sp.im(z) <= -upper else sp.Integer(0) for z in nodes]
    d = len(nodes)
    differences = [values]
    for k in range(1, d):
        row = [exact((differences[k-1][j+1]-differences[k-1][j]) /
                     (nodes[j+k]-nodes[j])) for j in range(d-k)]
        differences.append(row)
        bound = sp.Rational(2)**(k-1)/gap**k
        for j, dd in enumerate(row):
            require(abs_squared(dd) <= bound**2,
                    "Sharpened divided-difference bound failed.")
            if values[j] == values[j+k]:
                require(dd == 0, "A constant cluster has a nonzero difference.")
    x = sp.Symbol("x", real=True)
    polynomial, product = sp.Integer(0), sp.Integer(1)
    for k in range(d):
        polynomial += differences[k][0]*product
        product *= x-nodes[k]
    polynomial = sp.Poly(sp.expand(polynomial), x)
    coeff = [exact(polynomial.nth(k)) for k in range(n)]
    require(all(c.is_Rational for c in coeff), "Interpolant is not real rational.")
    for z, value in zip(nodes, values):
        require(exact(polynomial.eval(z)-value) == 0, "Interpolation value failed.")
    l1 = sum(abs(c) for c in coeff)
    coeff_bound_distinct = (4/gap)**(d-1)
    coeff_bound_n = (4*m/b)**(n-1)
    require(l1 <= coeff_bound_distinct <= coeff_bound_n,
            "Sharper coefficient l1 bound failed.")
    moments, h = hankel_from_roots(roots)
    q = sp.Matrix(coeff)
    quadratic = exact((q.T*h*q)[0])
    outer_count = sum(1 for z in roots if abs(sp.im(z)) >= upper)
    require(quadratic == -outer_count <= -2, "Negative witness identity failed.")
    norm_sq = sum(c*c for c in coeff)
    rayleigh_lower = -quadratic/norm_sq
    universal_lower = 2*(b/(4*m))**(2*n-2)
    require(rayleigh_lower >= universal_lower, "Universal lower estimate failed.")
    decision = rational_psd(h)
    require(not decision["is_psd"], "Nonreal example was incorrectly certified PSD.")
    return {
        "name": name, "n_counting_multiplicity": n, "distinct_nodes": d,
        "roots": [str(z) for z in roots], "b": str(b),
        "largest_gap": str(gap), "gap_lower_endpoint": str(lower),
        "gap_upper_endpoint": str(upper),
        "ordered_nodes": [str(z) for z in nodes],
        "prescribed_values": [str(v) for v in values],
        "divided_differences": [[str(v) for v in row] for row in differences],
        "polynomial": str(polynomial.as_expr()),
        "coefficients_low_to_high_padded_to_n": [str(c) for c in coeff],
        "coefficient_l1": str(l1),
        "coefficient_bound_distinct": str(coeff_bound_distinct),
        "coefficient_bound_n": str(coeff_bound_n),
        "moments": [str(s) for s in moments], "hankel": matrix_strings(h),
        "outer_root_count_with_multiplicity": outer_count,
        "quadratic_value": str(quadratic),
        "squared_coefficient_l2": str(norm_sq),
        "certified_D_lower_from_witness": str(rayleigh_lower),
        "theorem_D_lower": str(universal_lower),
        "rational_indefiniteness_certificate": decision,
    }


def primary_symbolic_certificate():
    t = sp.Symbol("t", positive=True)
    h = sp.Matrix([[3, t, t**2/2],
                   [t, t**2/2, t**3],
                   [t**2/2, t**3, 9*t**4/8]])
    roots = [t, I*t/2, -I*t/2]
    from_roots = sp.Matrix(3, 3, lambda i, j: sp.expand(sum(
        z**(i+j) for z in roots)))
    require(same_matrix(h, from_roots), "Primary moments do not match roots.")
    a, cross = h[:2, :2], h[:2, 2]
    schur = exact(h[2, 2]-(cross.T*a.inv()*cross)[0])
    correction = sp.Rational(25, 8)*t**4
    q = sp.Matrix([3*t**2/2, -5*t, 1])
    require(exact(a.det()-t**2/2) == 0, "Leading determinant failed.")
    require(exact(schur+correction) == 0, "Schur complement identity failed.")
    require(same_matrix(h*q, sp.Matrix([0, 0, -correction])),
            "Polynomial witness matrix identity failed.")
    require(exact((q.T*h*q)[0]+correction) == 0, "Primary quadratic value failed.")
    lower = sp.Matrix([[1, 0, 0], [t/3, 1, 0], [t**2/6, 5*t, 1]])
    diagonal = sp.diag(3, t**2/6, -correction)
    require(same_matrix(h, lower*diagonal*lower.T), "Primary LDL factorization failed.")
    repaired = h + sp.diag(0, 0, correction)
    repaired_diagonal = sp.diag(3, t**2/6, 0)
    require(same_matrix(repaired, lower*repaired_diagonal*lower.T),
            "Repaired PSD factorization failed.")
    norm_sq = exact((q.T*q)[0])
    require(norm_sq == 1+25*t**2+sp.Rational(9, 4)*t**4,
            "Primary witness norm failed.")
    return {
        "parameter_range": "0 < t <= 1", "roots": [str(z) for z in roots],
        "b": "t/2", "hankel": matrix_strings(h),
        "leading_2_by_2_first_pivot": "3",
        "leading_2_by_2_determinant": str(a.det()),
        "schur_complement": str(schur),
        "witness_coefficients_low_to_high": [str(c) for c in q],
        "witness_squared_norm": str(norm_sq),
        "quadratic_value": str(-correction),
        "LDL_lower": matrix_strings(lower),
        "LDL_diagonal": [str(diagonal[i, i]) for i in range(3)],
        "final_moment_correction": str(correction),
        "repaired_hankel": matrix_strings(repaired),
        "repaired_LDL_diagonal": [str(repaired_diagonal[i, i]) for i in range(3)],
        "exact_squeeze_for_D_over_t4": {
            "lower": "(25/8)/(1 + 25*t**2 + 9*t**4/4)", "upper": "25/8"},
        "limit_D_over_t4": "25/8",
        "note": "The limit follows from the exact squeeze; numerical values are illustrative.",
    }, h, t


def mp_rational(value):
    value = sp.Rational(value)
    return mp.mpf(int(value.p))/mp.mpf(int(value.q))


def write_scaling_table(path, symbolic_h, symbol_t):
    rows = []
    for k in range(11):
        tq = sp.Rational(1, 2**k)
        h = symbolic_h.subs(symbol_t, tq)
        eigenvalues = mp.eigsy(mp.matrix([[mp_rational(z) for z in row]
                                        for row in h.tolist()]), eigvals_only=True)
        t = mp_rational(tq)
        defect = -eigenvalues[0]
        require(defect > 0, "Illustrative primary eigenvalue is not negative.")
        correction = sp.Rational(25, 8)*tq**4
        repaired = h + sp.diag(0, 0, correction)
        require(rational_psd(repaired)["is_psd"], "Exact repaired matrix not PSD.")
        lower = mp.mpf(25)/8 / (1+25*t*t+mp.mpf(9)/4*t**4)
        ratio = defect/t**4
        slack = mp.power(10, -mp.mp.dps+12)
        require(lower-slack <= ratio <= mp.mpf(25)/8+slack,
                "Illustrative eigenvalue lies outside exact squeeze.")
        rows.append({
            "t_exact": str(tq), "b_exact": str(tq/2),
            "lambda_min": mp.nstr(eigenvalues[0], 60),
            "D": mp.nstr(defect, 60), "D_over_t4": mp.nstr(ratio, 60),
            "gap_to_25_over_8": mp.nstr(mp.mpf(25)/8-ratio, 60),
            "exact_squeeze_lower": str(sp.Rational(25, 8) /
                (1+25*tq**2+sp.Rational(9, 4)*tq**4)),
            "exact_squeeze_upper": "25/8",
            "theorem_D_lower_exact": str(2*(tq/8)**4),
            "theorem_D_upper_exact": str(30*(tq/2)**2),
            "final_moment_correction_exact": str(correction),
            "repair_psd_exact": True,
        })
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def psd_and_error_certificates():
    roots = [sp.Rational(-1, 2), sp.Integer(0), sp.Rational(1, 2)]
    moments, h = hankel_from_roots(roots)
    psd = rational_psd(h)
    require(psd["is_psd"], "Real-root example should be PSD.")
    require(psd["diagonal"] == ["3", "1/2", "1/24"], "Unexpected PSD pivots.")
    errors = [sp.Rational(k, 10**12) for k in range(5)]
    row_errors = [sum(errors[i+j] for j in range(3)) for i in range(3)]
    eta = max(row_errors)
    require(eta == sp.Rational(9, 10**12), "Hankel error row-sum failed.")
    b_bound = 4*(mp_rational(eta)/2)**mp.mpf("0.25")
    singular = rational_psd(sp.diag(3, 0, 0))
    zero_pivot_bad = rational_psd(sp.Matrix([[0, 1], [1, 0]]))
    negative_schur = rational_psd(sp.Matrix([[1, 2], [2, 1]]))
    require(singular["is_psd"], "Singular PSD zero-row case failed.")
    require(not zero_pivot_bad["is_psd"], "Zero-pivot nonzero-row case failed.")
    require(not negative_schur["is_psd"], "Negative Schur pivot case failed.")
    return {
        "real_roots": [str(z) for z in roots],
        "moments": [str(s) for s in moments], "hankel": matrix_strings(h),
        "PSD_certificate": psd,
        "conditional_interval_example": {
            "assumption": "Unknown true moments differ from these central moments by at most epsilon_k; true roots satisfy the theorem's hypotheses.",
            "epsilon_by_moment": [str(e) for e in errors],
            "matrix_error_row_sums": [str(e) for e in row_errors],
            "spectral_error_bound_eta": str(eta),
            "certified_D_upper": str(eta),
            "certified_b_upper_formula": "4*(eta/2)**(1/4)",
            "certified_b_upper_approx": mp.nstr(b_bound, 60),
        },
        "zero_pivot_handling": {
            "singular_PSD": singular,
            "zero_pivot_nonzero_row": zero_pivot_bad,
            "negative_Schur_pivot": negative_schur,
        },
    }


def upper_constant_certificate():
    n = sp.Symbol("n", integer=True, positive=True)
    j = sp.Symbol("j", integer=True)
    row_sum = sp.summation((n-1+j)*(n-2+j)/2, (j, 0, n-1))
    expected = n**2*(n-1)*(7*n-11)/6
    require(sp.simplify(n*row_sum-expected) == 0, "Upper constant identity failed.")
    return {"row_sum_times_n": str(sp.factor(n*row_sum)),
            "C_n": str(expected), "C_3": "30",
            "identity_checked_symbolically": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data")
    parser.add_argument("--precision", type=int, default=80)
    args = parser.parse_args()
    require(args.precision >= 50, "Use at least 50 decimal digits.")
    mp.mp.dps = args.precision
    args.data_dir.mkdir(parents=True, exist_ok=True)
    primary, symbolic_h, symbol_t = primary_symbolic_certificate()
    examples = [
        ("three_distinct_nodes", [sp.Rational(1, 2), I/4, -I/4]),
        ("separated_imaginary_levels", [sp.Rational(-1, 3),
             sp.Rational(1, 5)+I/5, sp.Rational(1, 5)-I/5,
             sp.Rational(-1, 4)+3*I/4, sp.Rational(-1, 4)-3*I/4]),
        ("nearby_nodes_in_same_cluster", [0, I/2, -I/2,
             sp.Rational(1, 1000)+I/2, sp.Rational(1, 1000)-I/2]),
        ("repeated_roots_counted_with_multiplicity", [0, 0, I/2, I/2, -I/2, -I/2]),
    ]
    cluster = [cluster_interpolation_certificate(name, roots) for name, roots in examples]
    psd = psd_and_error_certificates()
    constants = upper_constant_certificate()
    scaling = write_scaling_table(args.data_dir/"scaling_eigenvalues.csv",
                                  symbolic_h, symbol_t)
    certificate = {
        "title": "Exact finite Hankel root-detection certificates",
        "status": "All asserted exact identities and certificate checks passed.",
        "scope": "Supporting computations; not a proof-assistant formalization.",
        "versions": {"python": sys.version.split()[0], "sympy": sp.__version__,
                     "mpmath": mp.__version__, "eigenvalue_decimal_precision": mp.mp.dps},
        "theorem_normalization": {
            "root_radius_upper_bound": "1", "n": "degree counting multiplicity",
            "b": "maximum absolute imaginary part",
            "D": "max(0, -minimum eigenvalue of H)",
            "lower": "2*(b/(4*floor(n/2)))**(2*n-2)",
            "upper": "n**2*(n-1)*(7*n-11)*b**2/6",
            "inverse": "b <= 4*floor(n/2)*(D/2)**(1/(2*n-2))",
        },
        "primary_example": primary, "cluster_witnesses": cluster,
        "PSD_and_error_examples": psd, "upper_constant": constants,
        "scaling_table": {"file": "scaling_eigenvalues.csv", "rows": len(scaling),
                          "last_D_over_t4": scaling[-1]["D_over_t4"]},
    }
    output = args.data_dir/"exact_certificates.json"
    output.write_text(json.dumps(certificate, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print("PASS: symbolic primary example, Schur complement, negative witness and PSD repair")
    print(f"PASS: {len(cluster)} exact cluster-interpolation certificates, including repeated roots")
    print("PASS: rational PSD/indefiniteness certificates, both zero-pivot cases, error row sums")
    print("PASS: upper-constant identity and 11 eigenvalue illustrations at", mp.mp.dps, "digits")
    print("D/t^4 at t=1/1024:", scaling[-1]["D_over_t4"])
    print("Exact squeeze proves limiting value 25/8 = 3.125")
    print("Wrote", output)
    print("Wrote", args.data_dir/"scaling_eigenvalues.csv")


if __name__ == "__main__":
    main()
