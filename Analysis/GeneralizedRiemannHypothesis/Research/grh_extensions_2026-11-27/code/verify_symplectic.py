#!/usr/bin/env python3
"""Exact independent checks for rectangular Lagrangian projection laws.

Only the Python standard library is used.  Small cases enumerate actual
prescribed-Gram frames, not merely the closed formula being checked.  A
separate row reduction computes every matrix kernel and tests its isotropy.
The finite-field arithmetic includes GF(4)=F_2[x]/(x^2+x+1).

Run from any directory:
    python3 code/verify_symplectic.py
Results are written to results/symplectic_validation.json next to code/.
"""

from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import json
import sys
import time


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)


def product_factors(xs):
    answer = F(1)
    for x in xs:
        answer *= x
    return answer


def a(q, j):
    if j < 0:
        raise ValueError("a_j requires j >= 0")
    return product_factors(1 - F(1, q**i) for i in range(1, j + 1))


def C(q, n, b):
    assert b % 2 == 0 and b <= 2*n
    return product_factors(1 - F(1, q**(2*j))
                           for j in range(n-b//2+1, n+1))


def uniform_nullity(q, n, b, k):
    if k < max(0, b-n) or k > b:
        return F(0)
    return (F(1, q**(k*(n-b+k))) * a(q, n) * a(q, b)
            / (a(q, k) * a(q, n-b+k) * a(q, b-k)))


def R(q, b, k):
    if k > b//2:
        return F(0)
    return product_factors((1 - F(1, q**(b-2*i)))
                           / (1 - F(1, q**(b-i)))
                           for i in range(k))


def frame_count(q, n, b):
    # Count symplectic pairs recursively in successive orthogonal complements.
    z = 1
    for j in range(b//2):
        dimension = 2*(n-j)
        z *= (q**dimension-1)*q**(dimension-1)
    return z


def laws(q, n, b):
    normalizer = C(q, n, b)
    uniform = {k: uniform_nullity(q, n, b, k) for k in range(max(0,b-n), b+1)}
    constrained = {k: v*R(q,b,k)/normalizer for k,v in uniform.items()}
    assert sum(uniform.values()) == 1
    assert sum(constrained.values()) == 1
    overlap = sum(v * F(1, q**(k*(k-1)//2)) * R(q,b,k)
                  for k,v in uniform.items())
    rank_tv = sum(abs(constrained[k]-v) for k,v in uniform.items())/2
    chi2 = sum((constrained[k]-v)**2/v for k,v in uniform.items())
    return uniform, constrained, overlap, rank_tv, chi2


class Field:
    """Tiny table-based field, with polynomial-basis GF(4) explicitly supported."""

    def __init__(self, q):
        assert q in (2,3,4,5)
        self.q = q
        if q == 4:
            self.add = [[x ^ y for y in range(q)] for x in range(q)]
            self.neg = list(range(q))
            def multiply(x, y):
                z = 0
                while y:
                    if y & 1:
                        z ^= x
                    y >>= 1
                    x <<= 1
                    if x & 4:
                        x ^= 7
                return z
            self.mul = [[multiply(x,y) for y in range(q)] for x in range(q)]
        else:
            self.add = [[(x+y)%q for y in range(q)] for x in range(q)]
            self.neg = [(-x)%q for x in range(q)]
            self.mul = [[x*y%q for y in range(q)] for x in range(q)]
        self.inv = [0] + [next(y for y in range(1,q) if self.mul[x][y] == 1)
                          for x in range(1,q)]
        # Associativity/distributivity checks are cheap for these tiny tables.
        for x,y,z in product(range(q), repeat=3):
            assert self.mul[self.mul[x][y]][z] == self.mul[x][self.mul[y][z]]
            assert self.mul[x][self.add[y][z]] == self.add[self.mul[x][y]][self.mul[x][z]]

    def ambient_pair(self, x, y, n):
        out = 0
        for i in range(n):
            out = self.add[out][self.mul[x[i]][y[n+i]]]
            out = self.add[out][self.neg[self.mul[x[n+i]][y[i]]]]
        return out

    def source_pair(self, x, y):
        # H is diag(J_2,...,J_2), corresponding to ordered columns u1,v1,... .
        out = 0
        for i in range(0,len(x),2):
            out = self.add[out][self.mul[x[i]][y[i+1]]]
            out = self.add[out][self.neg[self.mul[x[i+1]][y[i]]]]
        return out

    def kernel(self, flat, n, b):
        matrix = [list(flat[i*b:(i+1)*b]) for i in range(n)]
        pivots = []
        row = 0
        for col in range(b):
            p = next((r for r in range(row,n) if matrix[r][col]), None)
            if p is None:
                continue
            matrix[row],matrix[p] = matrix[p],matrix[row]
            inverse = self.inv[matrix[row][col]]
            matrix[row] = [self.mul[inverse][x] for x in matrix[row]]
            for r in range(n):
                if r == row or matrix[r][col] == 0:
                    continue
                scalar = matrix[r][col]
                matrix[r] = [self.add[x][self.neg[self.mul[scalar][y]]]
                             for x,y in zip(matrix[r],matrix[row])]
            pivots.append(col)
            row += 1
            if row == n:
                break
        free = [j for j in range(b) if j not in pivots]
        basis = []
        for j in free:
            vector = [0]*b
            vector[j] = 1
            for i,pivot in enumerate(pivots):
                vector[pivot] = self.neg[matrix[i][j]]
            basis.append(tuple(vector))
        # Verify the returned vectors independently against the original rows.
        for vector in basis:
            for i in range(n):
                dot = 0
                for j in range(b):
                    dot = self.add[dot][self.mul[flat[i*b+j]][vector[j]]]
                assert dot == 0
        return basis


def decimal_string(x, digits=50):
    if not isinstance(x,F):
        x = F(x)
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def describe_fraction(x, digits=50):
    return {"exact": str(x), "decimal": decimal_string(x,digits)}


def enumerate_case(q, n, b):
    """Enumerate all ordered symplectic b-frames and every projected matrix."""
    started = time.monotonic()
    field = Field(q)
    vectors = list(product(range(q), repeat=2*n))
    pairing = [[field.ambient_pair(x,y,n) for y in vectors] for x in vectors]
    zero = vectors.index((0,)*(2*n))
    counts = Counter()
    total_frames = 0

    def recurse(complement, columns):
        nonlocal total_frames
        if len(columns) == b:
            matrix = tuple(vectors[columns[j]][i] for i in range(n) for j in range(b))
            counts[matrix] += 1
            total_frames += 1
            return
        for u in complement:
            if u == zero:
                continue
            for v in complement:
                if pairing[u][v] != 1:
                    continue
                if len(columns)+2 == b:
                    recurse((),columns+(u,v))
                else:
                    new_complement = tuple(w for w in complement
                                           if pairing[u][w] == 0 and pairing[v][w] == 0)
                    recurse(new_complement,columns+(u,v))

    recurse(tuple(range(len(vectors))),())
    expected_frames = frame_count(q,n,b)
    assert total_frames == expected_frames
    # Independent product formula for the same frame count.
    assert F(total_frames) == q**(2*n*b-b*(b-1)//2)*C(q,n,b)
    number_matrices = q**(n*b)
    uniform_mass = F(1,number_matrices)
    rank_u = Counter()
    rank_p = Counter()
    total_tv = F(0)
    nonisotropic_matrices = 0
    support_matrices = 0
    compared = 0
    for matrix in product(range(q),repeat=n*b):
        basis = field.kernel(matrix,n,b)
        k = len(basis)
        isotropic = all(field.source_pair(x,y) == 0
                        for i,x in enumerate(basis) for y in basis[i+1:])
        rank_u[k] += 1
        if isotropic:
            support_matrices += 1
            expected = F(expected_frames,number_matrices) * q**(k*(k-1)//2)/C(q,n,b)
            assert expected.denominator == 1
        else:
            nonisotropic_matrices += 1
            expected = F(0)
        observed = counts.get(matrix,0)
        assert observed == expected, (q,n,b,matrix,observed,expected)
        rank_p[k] += observed
        total_tv += abs(F(observed,total_frames)-uniform_mass)/2
        compared += 1

    predicted_u,predicted_p,overlap,rank_tv,chi2 = laws(q,n,b)
    for k in range(max(0,b-n),b+1):
        assert F(rank_u[k],number_matrices) == predicted_u[k]
        assert F(rank_p[k],total_frames) == predicted_p[k]
    actual_rank_tv = sum(abs(F(rank_p[k],total_frames)-F(rank_u[k],number_matrices))
                         for k in rank_u)/2
    actual_chi2 = sum((F(rank_p[k],total_frames)-F(rank_u[k],number_matrices))**2
                      / F(rank_u[k],number_matrices) for k in rank_u)
    assert actual_rank_tv == rank_tv
    assert actual_chi2 == chi2
    assert total_tv == 1-overlap == F(nonisotropic_matrices,number_matrices)
    assert support_matrices == len(counts)
    result = {
        "q": q, "n_rows": n, "b_columns": b, "c": b-n,
        "field": "GF(4), polynomial x^2+x+1" if q == 4 else "prime field",
        "enumerated_symplectic_frames": total_frames,
        "matrices_compared": compared,
        "matrices_in_support": support_matrices,
        "density_mismatches": 0,
        "rank_law_mismatches": 0,
        "full_tv": describe_fraction(total_tv),
        "rank_tv": describe_fraction(rank_tv),
        "chi_square_rank": describe_fraction(chi2),
        "elapsed_seconds": round(time.monotonic()-started,3),
    }
    print(f"PASS q={q}, n={n}, b={b}: {total_frames:,} frames; {compared:,} matrices",flush=True)
    return result


def B_decimal(q,h,digits=100):
    assert h % 2 == 0
    with localcontext() as ctx:
        ctx.prec = digits+10
        Q = Decimal(1)/q
        z = Decimal(1)
        j = h//2+1
        while Q**(2*j) > Decimal(10)**(-digits-5):
            z *= 1-Q**(2*j)
            j += 1
        return +z


def finite_metrics(q,n,c):
    b = n+c
    u,p,overlap,rank_tv,chi2 = laws(q,n,b)
    m = b//2
    D = product_factors(1-F(1,q**j) for j in range(n+1,n+c+1))
    E = product_factors(1-F(1,q**(2*j)) for j in range(m+1,n+1))
    exact_rank = a(q,n)/a(q,c)*(1/E-D)
    assert rank_tv == exact_rank
    assert p[c] > u[c]
    assert all(p[k] < u[k] for k in u if k > c)
    leading_rank = F(1,(q-1)*q**n)
    leading_chi2 = F(1,(q-1)*q**(2*n-c))
    scale = q**(2*n-c)
    with localcontext() as ctx:
        ctx.prec = 90
        normalized_overlap = (Decimal(overlap.numerator)/Decimal(overlap.denominator)
                              * Decimal(q)**(c*(c-1)//2) / B_decimal(q,n-c,100))
    return {
        "q":q,"n":n,"c":c,"b":b,"h":n-c,
        "rank_tv":describe_fraction(rank_tv),
        "full_overlap":describe_fraction(overlap),
        "rank_chi_square":describe_fraction(chi2),
        "rank_tv_over_asymptotic":describe_fraction(rank_tv/leading_rank),
        "chi_square_over_asymptotic":describe_fraction(chi2/leading_chi2),
        "overlap_over_asymptotic":str(normalized_overlap),
        "sample_complexity_scale":str(scale),
    }


def check_formula_grid():
    cases = 0
    max_rank_ratio_deviation = F(0)
    max_chi_ratio_deviation = F(0)
    for q in (2,3,4,5):
        for n in range(1,17):
            for c in range(1,n+1):
                if (n+c)%2:
                    continue
                row = finite_metrics(q,n,c)
                cases += 1
                if c >= 8:
                    rank_ratio = F(row["rank_tv_over_asymptotic"]["exact"])
                    chi_ratio = F(row["chi_square_over_asymptotic"]["exact"])
                    max_rank_ratio_deviation=max(max_rank_ratio_deviation,abs(rank_ratio-1))
                    max_chi_ratio_deviation=max(max_chi_ratio_deviation,abs(chi_ratio-1))
    print(f"PASS exact formula grid: {cases} parameter triples",flush=True)
    return {
        "q_values":[2,3,4,5],"n_range":[1,16],"cases":cases,
        "normalization_failures":0,"rank_sign_failures":0,"exact_rank_identity_failures":0,
        "max_rank_asymptotic_relative_error_for_c_ge_8":describe_fraction(max_rank_ratio_deviation),
        "max_chi_square_asymptotic_relative_error_for_c_ge_8":describe_fraction(max_chi_ratio_deviation),
    }


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).resolve().parents[1]/"results"/"symplectic_validation.json")
    args=parser.parse_args()
    cases=[(2,1,2),(2,2,2),(2,2,4),(2,3,4),
           (3,1,2),(3,2,2),(3,2,4),(4,1,2),(4,2,2)]
    enumerations=[enumerate_case(*case) for case in cases]
    grid=check_formula_grid()
    table=[finite_metrics(2,n,c) for n,c in [(8,4),(12,6),(20,10),(40,20),(12,12)]]
    asymptotic_sequences=[finite_metrics(q,c+h,c)
                          for q in (2,3,4,5) for c in (4,8,16,24)
                          for h in (0,2,2*c)]
    result={
        "description":"Independent exact finite-field enumeration and rational checks",
        "python_version":sys.version.split()[0],
        "dependencies":"Python standard library only",
        "enumeration_method":"Ordered symplectic pairs in successive orthogonal complements; independent matrix row reduction",
        "enumeration_cases":enumerations,
        "total_enumerated_frames":sum(x["enumerated_symplectic_frames"] for x in enumerations),
        "total_matrices_compared":sum(x["matrices_compared"] for x in enumerations),
        "formula_grid":grid,
        "requested_q2_table":table,
        "asymptotic_sequence_checks":asymptotic_sequences,
        "status":"PASS",
        "limitations":"Finite checks verify implementations and examples, not the all-parameter proof. GF(4) uses actual extension-field arithmetic in enumerations; q=4 grid identities use exact cardinality formulas.",
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(f"PASS total: {result['total_enumerated_frames']:,} frames, {result['total_matrices_compared']:,} matrices",flush=True)
    print(f"Results: {args.output}",flush=True)


if __name__ == "__main__":
    main()
