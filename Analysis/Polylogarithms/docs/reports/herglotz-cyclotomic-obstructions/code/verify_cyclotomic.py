#!/usr/bin/env python3
"""Exact certificates for the cyclotomic boundary kernel theorem.

Python 3.10+; standard library only. No floating-point ranks or PSLQ.

The paper proves that the linear relations among beta_q(a) are exactly those
among the integer matrices B_q(a)=P_a-P_(a^-1), with P_a the regular
permutation representation of (Z/q)^*/{+/-1}. The logarithmic Gram matrix
in the proof is positive definite for every q: every character is detected
by a primitive conductor shell. This program verifies the finite algebraic
consequences using exact arithmetic; it does not numerically prove the
analytic nonvanishing theorem used to establish that representation.

Run from any directory. Output is written to ../data relative to this file.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd
from pathlib import Path
import csv
import json


def factor(n: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def phi(n: int) -> int:
    result = n
    for p in factor(n):
        result = result//p*(p-1)
    return result


def root_counts_crt(q: int) -> tuple[int, int]:
    """Numbers of unit roots of x^2=+1 and x^2=-1 modulo q."""
    plus, minus = 1, 1
    for p, exponent in factor(q).items():
        if p == 2:
            plus *= 1 if exponent == 1 else 2 if exponent == 2 else 4
            minus *= 1 if exponent == 1 else 0
        else:
            plus *= 2
            minus *= 2 if p % 4 == 1 else 0
    return plus, minus


def rank_formula(q: int) -> int:
    if q <= 2:
        return 0
    plus, minus = root_counts_crt(q)
    numerator = phi(q)-plus-minus
    assert numerator % 4 == 0
    return numerator//4


def representatives(q: int) -> list[int]:
    return sorted({min(a, q-a) for a in range(1, q) if gcd(a, q) == 1})


def canonical(a: int, q: int) -> int:
    a %= q
    return min(a, (-a) % q)


def inverse(a: int, q: int) -> int:
    return canonical(pow(a, -1, q), q)


def add_sparse(target: dict[int, int], source: dict[int, int], multiplier=1):
    for index, coefficient in source.items():
        value = target.get(index, 0) + multiplier*coefficient
        if value:
            target[index] = value
        else:
            target.pop(index, None)


def boundary_matrix(q: int, n: int, reps: list[int]) -> dict[int, int]:
    """Sparse row-major integer matrix P_n-P_(n^-1)."""
    size = len(reps)
    index = {a: i for i, a in enumerate(reps)}
    n_inv = pow(n, -1, q)
    output: dict[int, int] = {}
    for row, a in enumerate(reps):
        first = row*size+index[canonical(a*n, q)]
        second = row*size+index[canonical(a*n_inv, q)]
        if first != second:
            output[first] = 1
            output[second] = -1
    return output


def rational_rank(columns: list[dict[int, int]]) -> int:
    """Sparse Gaussian elimination over Q, without a numerical tolerance."""
    pivots: dict[int, dict[int, Fraction]] = {}
    for column in columns:
        vector = {k: Fraction(v) for k, v in column.items()}
        while vector:
            pivot = min(vector)
            leading = vector[pivot]
            if pivot not in pivots:
                pivots[pivot] = {k: v/leading for k, v in vector.items()}
                break
            for k, v in pivots[pivot].items():
                value = vector.get(k, Fraction(0)) - leading*v
                if value:
                    vector[k] = value
                else:
                    vector.pop(k, None)
    return len(pivots)


def check_modulus(q: int, elimination: bool) -> dict:
    if q <= 2:
        return {"q": q, "phi": phi(q), "rank": 0, "trivial": True,
                "group_order": 1, "root_plus": 1, "root_minus": 1,
                "zero_representatives": [1], "rational_rank_checked": False}
    reps = representatives(q)
    inv = {a: inverse(a, q) for a in reps}
    columns = {a: boundary_matrix(q, a, reps) for a in reps}
    expected_rank = rank_formula(q)
    pairs = [(a, inv[a]) for a in reps if a < inv[a]]
    involutions = [a for a in reps if a == inv[a]]
    assert len(pairs) == expected_rank
    assert 2*len(pairs)+len(involutions) == len(reps)
    for a in reps:
        assert columns[inv[a]] == {k: -v for k, v in columns[a].items()}
        assert (not columns[a]) == (a*a % q in (1, q-1))
    # The first matrix row gives disjoint two-element supports for this basis.
    seen = set()
    size = len(reps)
    for a, _ in pairs:
        support = {k for k in columns[a] if k < size}
        assert len(support) == 2 and not (support & seen)
        seen.update(support)
    if elimination:
        assert rational_rank(list(columns.values())) == expected_rank
    units = [a for a in range(1, q) if gcd(a, q) == 1]
    plus = sum(a*a % q == 1 for a in units)
    minus = sum(a*a % q == q-1 for a in units)
    assert (plus, minus) == root_counts_crt(q)
    assert len(involutions) == (plus+minus)//2
    return {"q": q, "phi": phi(q), "group_order": len(reps),
            "root_plus": plus, "root_minus": minus,
            "rank": expected_rank, "trivial": expected_rank == 0,
            "zero_representatives": involutions,
            "inverse_pair_basis": [a for a, _ in pairs],
            "rational_rank_checked": elimination}


def preprint_counterexample() -> dict:
    """Exact p=7,n=2 defect of the printed untwisted three-term identity."""
    q, n = 7, 2
    reps = representatives(q)
    argument = n*pow(n+1, -1, q) % q
    first = boundary_matrix(q, n, reps)
    defect = dict(first)
    add_sparse(defect, boundary_matrix(q, n+1, reps), -1)
    add_sparse(defect, boundary_matrix(q, argument, reps), -1)
    assert argument == 3
    assert defect == {k: 3*v for k, v in first.items()}
    assert defect
    size = len(reps)
    matrix = [[defect.get(i*size+j, 0) for j in range(size)]
              for i in range(size)]
    return {"q": 7, "n": 2, "n_over_n_plus_one_mod_q": argument,
            "representatives": reps,
            "B_n_minus_B_n_plus_one_minus_B_quotient": matrix,
            "defect_equals": "3 B_7(2), which is nonzero",
            "original_boundary":
                "beta_7(2)=2(c_2 wedge c_1+c_3 wedge c_2+c_1 wedge c_3)",
            "scope": "Inspected arXiv:2012.15805v1 section 7.2; no claim about uninspected journal text."}


def boundary_first_row(q: int, n: int) -> dict[int, int]:
    """First row determines every regular-representation combination."""
    if q <= 2:
        return {}
    a, b = canonical(n, q), inverse(n, q)
    return {} if a == b else {a: 1, b: -1}


def check_j_family(limit: int) -> dict:
    """Exact normalized boundary blocks for J(2/q), q>=2.

    The paper derives the following boundary formulas from the RZ boundary
    and J(x)=F(2x)-2F(x)+F(x/2)+pi^2/(12x):
      q odd: beta_q(4)-2 beta_q(2);
      4|q:   0;
      q=2m, m odd: beta_m(2)-[2] wedge [m].
    Rational and cyclotomic blocks are separated by the normalized norm
    theorem in the paper. A zero cyclotomic block permits rational-dilog
    correction; a zero full boundary is the stronger condition.
    """
    rows = []
    for q in range(2, limit+1):
        rational_block: dict[int, int] = {}
        if q % 2:
            conductor = q
            cyclotomic_block = boundary_first_row(q, 4)
            add_sparse(cyclotomic_block, boundary_first_row(q, 2), -2)
            form = "beta_q(4)-2 beta_q(2)"
        elif q % 4 == 0:
            conductor = 1
            cyclotomic_block = {}
            form = "0 (three reciprocal-integer F arguments)"
        else:
            conductor = q//2
            cyclotomic_block = boundary_first_row(conductor, 2)
            rational_block = {p: -exponent
                              for p, exponent in factor(conductor).items()}
            assert all(p != 2 for p in rational_block)
            form = "beta_m(2)-[2] wedge [m], m=q/2 odd"
        full_zero = not cyclotomic_block and not rational_block
        rational_correction = not cyclotomic_block
        assert full_zero == (q in (2,3,5) or q % 4 == 0)
        assert rational_correction == (q in (2,3,5,6,10) or q % 4 == 0)
        rows.append({"q": q, "cyclotomic_conductor": conductor,
                     "boundary_form": form,
                     "cyclotomic_first_row": cyclotomic_block,
                     "rational_coefficients_on_2_wedge_p": rational_block,
                     "full_boundary_zero": full_zero,
                     "rational_dilog_correction_possible": rational_correction})
    return {"family": "J(2/q), q>=2",
            "verified_denominators": [2, limit],
            "full_boundary_zero_class": "{2,3,5} union {q:4 divides q}",
            "rational_dilog_correction_class": "{2,3,5,6,10} union {q:4 divides q}",
            "full_zero_count": sum(x["full_boundary_zero"] for x in rows),
            "rational_correction_count": sum(x["rational_dilog_correction_possible"]
                                             for x in rows),
            "checks": rows}


def main():
    output = Path(__file__).resolve().parents[1]/"data"
    output.mkdir(parents=True, exist_ok=True)
    detailed = [check_modulus(q, elimination=q <= 80) for q in range(1, 201)]
    rows = []
    for q in range(1, 1001):
        if q <= 2:
            plus, minus = 1, 1
        else:
            plus, minus = root_counts_crt(q)
        rank = rank_formula(q)
        rows.append({"q": q, "phi": phi(q), "roots_plus": plus,
                     "roots_minus": minus, "boundary_rank": rank})
    trivial = [row["q"] for row in rows if row["boundary_rank"] == 0]
    assert trivial == [1,2,3,4,5,6,8,10,12,24]
    report = {
        "method": "Exact integer regular-representation matrices and rational Gaussian elimination",
        "logical_scope": "Finite verification of consequences of the proved all-modulus Gram theorem; no numerical transcendence assertion.",
        "detailed_moduli": [1,200],
        "exact_rational_elimination_moduli": [3,80],
        "closed_formula_moduli": [1,1000],
        "all_boundary_zero_moduli_in_verified_range": trivial,
        "checks": detailed,
        "preprint_three_term_counterexample": preprint_counterexample(),
        "J_two_over_q": check_j_family(1000),
    }
    (output/"cyclotomic_checks.json").write_text(json.dumps(report, indent=2)+"\n")
    with (output/"rank_table.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({"status":"passed", "detailed_moduli":len(detailed),
                      "rank_table_rows":len(rows), "output":str(output)}))


if __name__ == "__main__":
    main()
