#!/usr/bin/env python3
"""Exact finite regression checks for triangular Hahn differential systems.

This program does not implement arbitrary infinite Hahn supports or verify the
manuscript in a proof assistant. Numerical remainder illustrations are marked
separately from the exact rational/symbolic assertions.

Run from any directory. Recorded output is preserved: default output is rerun/.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
import random
from collections import Counter
from pathlib import Path
from typing import Any

import mpmath as mp
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

SEED = 20260929
RNG = random.Random(SEED)
COUNTS: Counter[str] = Counter()
CASES: dict[str, list[Any]] = {}
z = sp.Symbol("z")
s = sp.Symbol("s", positive=True)
t = sp.Symbol("t", positive=True)


def check(condition: Any, group: str, description: str) -> None:
    if not bool(condition):
        raise AssertionError(f"{group}: {description}")
    COUNTS[group] += 1


def matrix_zero(A: sp.MatrixBase) -> bool:
    return all(sp.cancel(e) == 0 for e in A)


def equal(A: sp.MatrixBase, B: sp.MatrixBase, group: str, label: str) -> None:
    check(A.shape == B.shape and matrix_zero(A - B), group, label)


def rat() -> sp.Rational:
    return sp.Rational(RNG.randint(-3, 3), RNG.randint(1, 3))


def random_matrix(rows: int, cols: int) -> sp.Matrix:
    return sp.Matrix(rows, cols, lambda i, j: rat())


def toeplitz(coefficients: list[sp.Matrix], degree: int) -> sp.Matrix:
    r = coefficients[0].rows
    result = sp.zeros(r * (degree + 1))
    for i in range(degree + 1):
        for j in range(i, degree + 1):
            if j - i < len(coefficients):
                result[i*r:(i+1)*r, j*r:(j+1)*r] = coefficients[j-i]
    return result


def target(b: sp.Matrix, degree: int) -> sp.Matrix:
    return b.col_join(sp.zeros(b.rows * degree, 1))


def soluble(A: sp.Matrix, b: sp.Matrix) -> bool:
    return A.rank() == A.row_join(b).rank()


def certify(A: sp.Matrix, b: sp.Matrix, group: str) -> dict[str, Any]:
    """Return and independently multiply a positive or negative rational witness."""
    if soluble(A, b):
        solution, parameters = A.gauss_jordan_solve(b)
        solution = solution.subs({p: 0 for p in parameters})
        equal(A * solution, b, group, "positive certificate multiplication")
        return {"kind": "positive", "vector": [str(v) for v in solution]}
    for w in A.T.nullspace():
        if (w.T * b)[0] != 0:
            equal(w.T * A, sp.zeros(1, A.cols), group,
                  "negative certificate annihilates matrix")
            check((w.T * b)[0] != 0, group, "negative certificate separates forcing")
            return {"kind": "negative", "vector": [str(v) for v in w],
                    "pairing": str((w.T * b)[0])}
    raise AssertionError("Insoluble rational system had no separating nullvector")


def add_dict(a: dict[tuple[int, ...], sp.Rational],
             b: dict[tuple[int, ...], sp.Rational]) -> dict[tuple[int, ...], sp.Rational]:
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, sp.S.Zero) + c
        if out[e] == 0:
            del out[e]
    return out


def derivative_monomial(e: tuple[int, ...], c: sp.Rational = sp.S.One
                        ) -> dict[tuple[int, ...], sp.Rational]:
    out: dict[tuple[int, ...], sp.Rational] = {}
    for j, power in enumerate(e):
        if power:
            dest = tuple(v - (i <= j) for i, v in enumerate(e))
            out = add_dict(out, {dest: c * power})
    return out


def shift_dict(a: dict[tuple[int, ...], sp.Rational], shift: tuple[int, ...]
               ) -> dict[tuple[int, ...], sp.Rational]:
    return {tuple(v + w for v, w in zip(e, shift)): c for e, c in a.items()}


def scalar_checks() -> None:
    group = "scalar_support_and_identities"
    for n in range(4):
        for _ in range(25):
            e = tuple(RNG.randint(-4, 4) for _ in range(n + 1))
            f = tuple(RNG.randint(-4, 4) for _ in range(n + 1))
            de = derivative_monomial(e)
            check(de.get(tuple([-1] * (n + 1)), 0) == 0, group,
                  "monomial derivative has zero deepest residue")
            left = derivative_monomial(tuple(v + w for v, w in zip(e, f)))
            right = add_dict(shift_dict(de, f), shift_dict(derivative_monomial(f), e))
            check(left == right, group, "Leibniz rule for finite monomials")
    for alpha in (sp.Rational(-2), sp.Rational(1), sp.Rational(2, 3)):
        for power in range(-3, 4):
            g = t**power
            for count in range(1, 6):
                primitive = sum((-1)**j * sp.diff(g, t, j) / alpha**(j+1)
                                for j in range(count))
                residual = alpha * primitive + sp.diff(primitive, t) - g
                expected = (-1)**(count-1) * sp.diff(g, t, count) / alpha**count
                check(sp.simplify(residual - expected) == 0, group,
                      "finite geometric inverse has exact tail")
    CASES[group] = [{"log_depths": [0, 1, 2, 3], "monomial_pairs": 100,
                     "geometric_inverse_truncations": 105}]


def graph_bounds(N: sp.Matrix, regular: list[bool]) -> tuple[int, int]:
    m = len(regular)
    lengths = [0] * m
    weights = [0] * m
    for i in reversed(range(m)):
        children = [j for j in range(i+1, m)
                    if not matrix_zero(N[2*i:2*i+2, 2*j:2*j+2])]
        lengths[i] = max([0] + [1 + lengths[j] for j in children])
        weights[i] = int(regular[i]) + max([0] + [weights[j] for j in children])
    return max(lengths, default=0), max(weights, default=0)


def word_coefficient(P: sp.Matrix, G: sp.Matrix, N: sp.Matrix,
                     R: sp.Matrix, K: sp.Matrix, j: int, ell: int) -> sp.Matrix:
    total = sp.zeros(P.rows, K.cols)
    for n_letters in range(ell + 1):
        length = n_letters + j
        if length == 0:
            continue
        for positions in itertools.combinations(range(length), j):
            r_positions = set(positions)
            product = P
            for index in range(length):
                product = product * (R if index in r_positions else N)
                if index < length - 1:
                    product = product * G
            total += (-1)**(length - 1) * product * K
    return total


def finite_defect_checks() -> None:
    group = "finite_defect_models"
    records = []
    for m in range(1, 5):
        for case in range(5):
            regular = [bool(RNG.randrange(2)) for _ in range(m)]
            if case == 0:
                regular = [True] * m
            if case == 1:
                regular = [False] * m
            r = sum(regular)
            D = sp.zeros(2*m)
            G = sp.zeros(2*m)
            R = sp.zeros(2*m)
            N = sp.zeros(2*m)
            K = sp.zeros(2*m, r)
            index = 0
            for i, split in enumerate(regular):
                lam = sp.Rational(RNG.choice([-3, -2, 1, 2, 3]))
                if split:
                    Di = sp.diag(0, lam)
                    Gi = sp.diag(0, 1/lam)
                    Ri = sp.diag(1, rat())
                    K[2*i, index] = 1
                    index += 1
                else:
                    Di = sp.Matrix([[lam, rat()], [0, RNG.choice([1, 2, 3])]])
                    Gi = Di.inv()
                    Ri = random_matrix(2, 2)
                D[2*i:2*i+2, 2*i:2*i+2] = Di
                G[2*i:2*i+2, 2*i:2*i+2] = Gi
                R[2*i:2*i+2, 2*i:2*i+2] = Ri
                for j in range(i+1, m):
                    if RNG.random() < 0.75:
                        N[2*i:2*i+2, 2*j:2*j+2] = random_matrix(2, 2)
            P, E, Q = K.T, K.T, K
            one = sp.eye(2*m)
            equal(D*G, one-Q*P, group, "D G splitting")
            equal(G*D, one-K*E, group, "G D splitting")
            equal(E*G, sp.zeros(r, 2*m), group, "E G normalization")
            equal(G*Q, sp.zeros(2*m, r), group, "G Q normalization")
            equal(P*R*K, sp.eye(r), group, "crossing identity")
            equal(G*R*K, sp.zeros(2*m, r), group, "G R K vanishes")
            equal(P*R*G, sp.zeros(r, 2*m), group, "P R G vanishes")
            ell, q = graph_bounds(N, regular)
            S0 = sum(((-G*N)**j for j in range(m)), sp.zeros(2*m))
            H0 = sum(((-N*G)**j for j in range(m)), sp.zeros(2*m))
            equal(S0*(one+G*N), one, group, "finite inverse on left")
            equal((one+G*N)*S0, one, group, "finite inverse on right")
            M0 = P*N*S0*K
            L = D+N
            check(2*m-L.rank() == r-M0.rank(), group, "fixed-depth kernel count")
            y = random_matrix(2*m, 1)
            f = L*y
            b = P*H0*f
            c = E*y
            equal(M0*c, b, group, "ground-truth solution projects to obstruction")
            equal(S0*G*f+S0*K*c, y, group, "ground-truth solution reconstructs")
            f_test = random_matrix(2*m, 1)
            b_test = P*H0*f_test
            check(soluble(L, f_test) == soluble(M0, b_test), group,
                  "arbitrary forcing range equivalence")
            if r:
                max_j = max(q, 2)
                Scoeff = [S0]
                for j in range(1, max_j+1):
                    Scoeff.append(-S0*G*R*Scoeff[-1])
                Mcoeff = [P*N*Scoeff[j]*K +
                          (P*R*Scoeff[j-1]*K if j else sp.zeros(r))
                          for j in range(max_j+1)]
                for j in range(max_j+1):
                    expected_diag = sp.eye(r) if j == 1 else sp.zeros(r)
                    check(all(Mcoeff[j][i, i] == expected_diag[i, i] for i in range(r)),
                          group, "diagonal is exactly z")
                    check(all(Mcoeff[j][i, k] == 0 for i in range(r)
                              for k in range(i)), group, "compressed matrix is upper triangular")
                for j in range(3):
                    equal(Mcoeff[j], word_coefficient(P, G, N, R, K, j, ell),
                          group, "independent finite word expansion")
                for degree in range(q+1):
                    small = toeplitz(Mcoeff, degree)
                    full = toeplitz([L, R], degree)
                    check(small.cols-small.rank() == full.cols-full.rank(), group,
                          "full and reduced polynomial kernels agree")
                    check(soluble(small, target(b_test, degree)) ==
                          soluble(full, target(f_test, degree)), group,
                          "full and reduced polynomial ranges agree")
                check(soluble(toeplitz(Mcoeff, q), target(b_test, q)), group,
                      "path-bound degree always solves")
                C = toeplitz(Mcoeff, q-1)
                check(C.cols-C.rank() == r, group, "homogeneous path bound saturates dimension")
            records.append({"coordinates": m, "split_pattern": regular,
                            "r": r, "q": q, "longest_path_edges": ell,
                            "M0_rank": M0.rank()})
    CASES[group] = records


def partitions(n: int, maximum: int | None = None):
    if n == 0:
        yield []
        return
    if maximum is None:
        maximum = n
    for first in range(min(n, maximum), 0, -1):
        for tail in partitions(n-first, first):
            yield [first] + tail


def jordan_checks() -> None:
    group = "jordan_and_certificate_checks"
    records = []
    for r in range(1, 7):
        for parts in partitions(r):
            J = sp.zeros(r)
            last_indices = []
            offset = 0
            for size in parts:
                for j in range(size-1):
                    J[offset+j, offset+j+1] = 1
                last_indices.append(offset+size-1)
                offset += size
            coeff = [-J, sp.eye(r)]
            b = sp.zeros(r, 1)
            b[last_indices[0]] = 1  # first block has the largest size
            for d in range(max(parts)+1):
                C = toeplitz(coeff, d)
                check(C.cols-C.rank() == sum(min(d+1, size) for size in parts), group,
                      "Toeplitz nullity equals Jordan formula")
                check(soluble(C, target(b, d)) == (d >= parts[0]), group,
                      "terminal forcing has exactly the block length degree")
            minimum = parts[0]
            positive = certify(toeplitz(coeff, minimum), target(b, minimum), group)
            negative = certify(toeplitz(coeff, minimum-1), target(b, minimum-1), group)
            check(positive["kind"] == "positive" and negative["kind"] == "negative", group,
                  "paired minimality certificate")
            records.append({"r": r, "blocks": parts, "minimum_degree": minimum})
    CASES[group] = records


def generic_matrix_series_checks() -> None:
    group = "generic_triangular_matrix_series"
    records = []
    for r in range(1, 6):
        for _ in range(4):
            coeff = [sp.zeros(r), sp.eye(r), sp.zeros(r)]
            for j in range(3):
                for row in range(r):
                    for col in range(row+1, r):
                        coeff[j][row, col] = rat()
            M = sum((coeff[j]*z**j for j in range(3)), sp.zeros(r))
            check(sp.expand(M.det()) == z**r, group, "determinant z^r")
            S = smith_normal_form(M, domain=sp.QQ.poly_ring(z))
            indices = []
            for i in range(r):
                polynomial = sp.Poly(S[i, i], z)
                terms = polynomial.terms()
                check(len(terms) == 1, group, "Smith factors are monomials")
                indices.append(terms[0][0][0])
            check(sum(indices) == r, group, "total Smith order")
            h = []
            for d in range(r):
                C = toeplitz(coeff, d)
                nullity = C.cols-C.rank()
                h.append(nullity)
                check(nullity == sum(min(d+1, nu) for nu in indices), group,
                      "independent Smith form matches Toeplitz nullity")
            recovered = []
            previous = 0
            increments = []
            for value in h:
                increments.append(value-previous)
                previous = value
            increments.append(0)
            for k in range(1, r+1):
                recovered.extend([k]*(increments[k-1]-increments[k]))
            recovered.extend([0]*(r-len(recovered)))
            check(sorted(recovered) == sorted(indices), group,
                  "bounded jet recovers complete Smith multiset")
            b = random_matrix(r, 1)
            minimum = next(d for d in range(r+1)
                           if soluble(toeplitz(coeff, d), target(b, d)))
            certify(toeplitz(coeff, minimum), target(b, minimum), group)
            if minimum:
                certify(toeplitz(coeff, minimum-1), target(b, minimum-1), group)
            records.append({"r": r, "smith_indices": sorted(indices),
                            "homogeneous_nullities": h, "forcing_minimum": minimum})
    CASES[group] = records


def mixed_checks() -> None:
    group = "mixed_system_symbolic_checks"
    c = sp.Symbol("c")
    vf = sp.Function("v")(s)
    jf = sp.Function("J")(s)
    T = 2*sp.log(s)
    y1 = (1-c)*T**2/2-jf
    y2 = -T+vf
    y3 = T
    substitutions = {sp.diff(vf, s): 2*vf+2/s, sp.diff(jf, s): 2*vf/s}
    equations = [sp.diff(y1, s)+2*y2/s+2*c*y3/s,
                 sp.diff(y2, s)-2*y2-2*y3,
                 sp.diff(y3, s)-2/s]
    for equation in equations:
        check(sp.simplify(equation.subs(substitutions)) == 0, group,
              "symbolic exact particular solution")
    for N in range(1, 13):
        vn = -sum((-1)**j*sp.factorial(j)/(2**j*s**(j+1)) for j in range(N))
        jn = 2*sum((-1)**j*sp.factorial(j)/(2**j*(j+1)*s**(j+1)) for j in range(N))
        residual = sp.diff(vn, s)-2*vn-2/s
        expected = (-1)**(N-1)*sp.factorial(N)/(2**(N-1)*s**(N+1))
        check(sp.simplify(residual-expected) == 0, group, "exact factorial tail residual")
        check(sp.simplify(sp.diff(jn, s)-2*vn/s) == 0, group, "finite primitive coefficients")
    for K in range(9):
        a = sp.S.One
        w = sp.S.One
        for k in range(1, K+1):
            a *= z-sp.Rational(k-1, 2)
            w += a/s**k
        residual = sp.diff(w, s)-2*w+2*z*w/s+2
        expected = (2*z-K)*a/s**(K+1)
        check(sp.cancel(residual-expected) == 0, group, "exact w(z) falling-factor tail")
        check(sp.limit(w, s, sp.oo) == 1, group, "constant term of transfer is one")
    mixed_records = []
    for value in (-2, 0, 1, 2, sp.Rational(3, 2)):
        eta = value-1
        coeff = [sp.Matrix([[0, eta], [0, 0]]), sp.eye(2)]
        b = sp.Matrix([0, 1])
        C1 = toeplitz(coeff, 1)
        row = sp.Matrix([[0, -eta, 1, 0]])
        equal(row*C1, sp.zeros(1, 4), group, "explicit dual row annihilation")
        check((row*target(b, 1))[0] == -eta, group, "explicit dual pairing")
        minimum = 1 if value == 1 else 2
        check(not soluble(toeplitz(coeff, minimum-1), target(b, minimum-1)), group,
              "mixed minimum lower degree excluded")
        check(soluble(toeplitz(coeff, minimum), target(b, minimum)), group,
              "mixed minimum attained")
        mixed_records.append({"c": str(value), "minimum_degree": minimum,
                              "positive": certify(toeplitz(coeff, minimum),
                                                  target(b, minimum), group),
                              "negative": certify(toeplitz(coeff, minimum-1),
                                                  target(b, minimum-1), group)})
    CASES[group] = mixed_records


def numerical_illustrations() -> list[dict[str, Any]]:
    mp.mp.dps = 75
    output = []
    for s0 in (mp.mpf('0.5'), mp.mpf(1), mp.mpf(2), mp.mpf(5), mp.mpf(10), mp.mpf(20)):
        def v(x):
            return -2*mp.exp(2*x)*mp.e1(2*x)
        v_exact = v(s0)
        j_exact = -2*mp.quad(lambda x: v(x)/x, [s0, 2*s0, 10*s0, mp.inf])
        for N in (0, 1, 2, 4, 8, 12):
            vn = -sum(((-1)**j*mp.factorial(j)/(2**j*s0**(j+1)) for j in range(N)), mp.mpf(0))
            jn = 2*sum(((-1)**j*mp.factorial(j)/(2**j*(j+1)*s0**(j+1))
                        for j in range(N)), mp.mpf(0))
            vb = mp.factorial(N)/(2**N*s0**(N+1))
            jb = 2*vb/(N+1)
            rv = (-1)**(N+1)*(v_exact-vn)/vb
            rj = (-1)**N*(j_exact-jn)/jb
            if not (0 < rv <= 1+mp.mpf('1e-55') and 0 < rj <= 1+mp.mpf('1e-55')):
                raise AssertionError(f"Numerical illustration failed at s={s0}, N={N}")
            output.append({"s": str(s0), "N": N,
                           "signed_v_error_div_bound": mp.nstr(rv, 25),
                           "signed_J_error_div_bound": mp.nstr(rj, 25)})
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1]/"rerun")
    parser.add_argument("--skip-numerical", action="store_true",
                        help="Run only exact algebraic tests.")
    args = parser.parse_args()
    scalar_checks()
    finite_defect_checks()
    jordan_checks()
    generic_matrix_series_checks()
    mixed_checks()
    numbers = [] if args.skip_numerical else numerical_illustrations()
    output = {
        "status": "PASS",
        "seed": SEED,
        "environment": {"python": platform.python_version(), "sympy": sp.__version__,
                        "mpmath": mp.__version__},
        "exact_assertions": sum(COUNTS.values()),
        "exact_assertions_by_group": dict(COUNTS),
        "case_counts": {key: len(value) for key, value in CASES.items()},
        "exact_cases": CASES,
        "numerical_illustrations": {
            "status": "SKIPPED" if args.skip_numerical else "PASS",
            "working_decimal_digits": mp.mp.dps,
            "case_count": len(numbers),
            "interval_arithmetic": False,
            "cases": numbers,
        },
        "scope": ["Finite exact regression tests, not a proof of arbitrary Hahn supports.",
                  "No Lean or other proof-assistant verification is performed.",
                  "Random formal matrix series are not claimed as differential realizations.",
                  "Analytic inequalities are proved in the manuscript; floating-point checks are illustrative."],
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    with (args.output_dir/"results.json").open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(output, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    summary = (
        "\\begin{center}\\small\n"
        "\\begin{tabular}{lr}\\toprule\n"
        "Completed check category & Recorded count\\\\\\midrule\n"
        f"Exact rational/symbolic assertions & {sum(COUNTS.values()):,}\\\\\n"
        f"Finite-defect models & {len(CASES['finite_defect_models'])}\\\\\n"
        f"Jordan profiles with paired degree certificates & {len(CASES['jordan_and_certificate_checks'])}\\\\\n"
        f"General triangular polynomial matrix-series cases & {len(CASES['generic_triangular_matrix_series'])}\\\\\n"
        f"Mixed-system parameter cases & {len(CASES['mixed_system_symbolic_checks'])}\\\\\n"
        f"High-precision analytic illustrations & {len(numbers)}\\\\\n"
        "\\bottomrule\\end{tabular}\\end{center}\n"
        f"The recorded run used Python {platform.python_version()}, SymPy {sp.__version__}, "
        f"and mpmath {mp.__version__}, with seed {SEED}. "
        "All recorded checks passed. Counts of cases are not meant to sum to the assertion total; "
        "each case includes several independently checked identities.\n"
    )
    with (args.output_dir/"summary.tex").open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(summary)
    print(json.dumps({"status": "PASS", "exact_assertions": output["exact_assertions"],
                      "case_counts": output["case_counts"], "numerical_cases": len(numbers),
                      "output": str(args.output_dir)}, indent=2))


if __name__ == "__main__":
    main()
