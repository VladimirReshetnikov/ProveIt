#!/usr/bin/env python3
"""Independent exhaustive checks for complementary symplectic matrix blocks.

No third-party packages are required.  GF(4) is GF(2)[x]/(x^2+x+1),
not arithmetic modulo four.  For every listed (q,a,b), this program visits
every A in Mat_{a,b}(F_q) and every B in Mat_{b,b}(F_q) separately.
Grouping B by its exact Gram matrix counts every solution of
    A^t J_a A + B^t J_b B = J_b
without an impractical quadratic enumeration of all (A,B) pairs.
The Gram condition implies injectivity, since J_b is nonsingular.

Only after these counts are obtained are they compared against the exact
embedding, likelihood, kernel-moment and defect-moment formulas.
The script verifies finite formulas, not the infinite asymptotic theorem.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import csv
import json


class FiniteField:
    def __init__(self, q):
        assert q in (2, 3, 4, 5)
        self.q = q
        self.add = [[0] * q for _ in range(q)]
        self.mul = [[0] * q for _ in range(q)]
        for x in range(q):
            for y in range(q):
                if q == 4:
                    self.add[x][y] = x ^ y
                    # a+b*x, with x^2=x+1 in characteristic two.
                    a, b, c, d = x & 1, x >> 1, y & 1, y >> 1
                    self.mul[x][y] = ((a*c) ^ (b*d)) | (((a*d) ^ (b*c) ^ (b*d)) << 1)
                else:
                    self.add[x][y] = (x + y) % q
                    self.mul[x][y] = x * y % q
        self.neg = [next(y for y in range(q) if self.add[x][y] == 0) for x in range(q)]
        self.inv = [0] + [next(y for y in range(1, q) if self.mul[x][y] == 1) for x in range(1, q)]
        # Verify the arithmetic independently before using it.
        for x, y, z in product(range(q), repeat=3):
            assert self.add[self.add[x][y]][z] == self.add[x][self.add[y][z]]
            assert self.mul[self.mul[x][y]][z] == self.mul[x][self.mul[y][z]]
            assert self.mul[x][self.add[y][z]] == self.add[self.mul[x][y]][self.mul[x][z]]

    def sub(self, x, y):
        return self.add[x][self.neg[y]]

    def rank(self, matrix, rows, cols):
        a = [list(matrix[i*cols:(i+1)*cols]) for i in range(rows)]
        r = 0
        for j in range(cols):
            pivot = next((i for i in range(r, rows) if a[i][j]), None)
            if pivot is None:
                continue
            a[r], a[pivot] = a[pivot], a[r]
            inverse = self.inv[a[r][j]]
            a[r] = [self.mul[inverse][v] for v in a[r]]
            for i in range(r+1, rows):
                coefficient = a[i][j]
                if coefficient:
                    a[i] = [self.sub(v, self.mul[coefficient][w]) for v, w in zip(a[i], a[r])]
            r += 1
            if r == rows:
                break
        return r

    def gram(self, matrix, rows, cols):
        """Upper triangle of M^t J_rows M for interleaved symplectic pairs."""
        result = []
        for i in range(cols):
            for j in range(i+1, cols):
                value = 0
                for r in range(0, rows, 2):
                    positive = self.mul[matrix[r*cols+i]][matrix[(r+1)*cols+j]]
                    negative = self.mul[matrix[(r+1)*cols+i]][matrix[r*cols+j]]
                    value = self.add[value][self.sub(positive, negative)]
                result.append(value)
        return tuple(result)

    def alternating_matrix(self, triangle, size):
        a = [0] * (size*size)
        index = 0
        for i in range(size):
            for j in range(i+1, size):
                a[i*size+j] = triangle[index]
                a[j*size+i] = self.neg[triangle[index]]
                index += 1
        return a


def canonical_triangle(size):
    return tuple(int(i % 2 == 0 and j == i+1) for i in range(size) for j in range(i+1, size))


@lru_cache(None)
def gaussian(q, n, k):
    if k < 0 or k > n:
        return 0
    answer = F(1)
    for i in range(k):
        answer *= F(q**(n-i)-1, q**(k-i)-1)
    assert answer.denominator == 1
    return answer.numerator


def qpower(q, exponent):
    return F(q**exponent) if exponent >= 0 else F(1, q**(-exponent))


@lru_cache(None)
def eta(q, half_dimension):
    answer = F(1)
    for j in range(1, half_dimension+1):
        answer *= 1 - F(1, q**(2*j))
    return answer


@lru_cache(None)
def gl_order(q, dimension):
    answer = 1
    for j in range(dimension):
        answer *= q**dimension - q**j
    return answer


@lru_cache(None)
def sp_order(q, dimension):
    assert dimension % 2 == 0
    m = dimension // 2
    answer = q**(m*m)
    for j in range(1, m+1):
        answer *= q**(2*j)-1
    return answer


@lru_cache(None)
def embeddings(q, ambient, dimension, half_rank):
    assert ambient % 2 == 0
    if half_rank < 0 or 2*half_rank > dimension or dimension-half_rank > ambient//2:
        return 0
    answer = qpower(q, ambient*dimension - dimension*(dimension-1)//2)
    for j in range(ambient//2-dimension+half_rank+1, ambient//2+1):
        answer *= 1 - F(1, q**(2*j))
    assert answer.denominator == 1
    return answer.numerator


def subspace_type_count(q, ambient, dimension, half_rank):
    radical = dimension - 2*half_rank
    numerator = embeddings(q, ambient, dimension, half_rank)
    denominator = sp_order(q, 2*half_rank) * gl_order(q, radical) * q**(2*half_rank*radical)
    answer = F(numerator, denominator)
    assert answer.denominator == 1
    return answer.numerator


def gaussian_moments(q, law):
    return [sum((gaussian(q, k, j)*prob for k, prob in enumerate(law)), F(0)) for j in range(len(law))]


def invert_gaussian_moments(q, moments):
    size = len(moments)
    answer = [F(0)]*size
    for j in reversed(range(size)):
        answer[j] = moments[j] - sum((gaussian(q, k, j)*answer[k] for k in range(j+1, size)), F(0))
    return answer


def tv(first, second):
    return sum((abs(a-b) for a, b in zip(first, second)), F(0))/2


def stringify(values):
    return [str(x) for x in values]


@lru_cache(None)
def b_gram_counts(q, b):
    field = FiniteField(q)
    counts = Counter(field.gram(B, b, b) for B in product(range(q), repeat=b*b))
    assert sum(counts.values()) == q**(b*b)
    return counts


def run_case(q, a, b):
    assert a >= b >= 2 and a % 2 == b % 2 == 0
    field = FiniteField(q)
    gram_counts = b_gram_counts(q, b)
    total_a = q**(a*b)
    target = canonical_triangle(b)
    iid_kernel_counts = Counter()
    frame_kernel_counts = Counter()
    defect_counts = Counter()
    frame_defect_counts = Counter()
    # Aggregate the exact number of A's with each completion multiplicity.
    completion_hist = Counter()
    total_frames = 0
    gram_rank = {}
    likelihood_checked = set()
    alpha = eta(q, b//2)*eta(q, a//2)/eta(q, (a+b)//2)
    formula_frames = embeddings(q, a+b, b, b//2)

    for A in product(range(q), repeat=a*b):
        gram = field.gram(A, a, b)
        residual = tuple(field.sub(x, y) for x, y in zip(target, gram))
        completions = gram_counts.get(residual, 0)
        total_frames += completions
        nullity = b-field.rank(A, a, b)
        iid_kernel_counts[nullity] += 1
        frame_kernel_counts[nullity] += completions
        if residual not in gram_rank:
            gram_rank[residual] = field.rank(field.alternating_matrix(residual, b), b, b)
        defect_nullity = b-gram_rank[residual]
        assert defect_nullity % 2 == 0
        defect_counts[defect_nullity] += 1
        frame_defect_counts[defect_nullity] += completions
        completion_hist[completions] += 1

        if residual not in likelihood_checked:
            ell = defect_nullity//2
            formula_completions = sum(gaussian(q, defect_nullity, k)*embeddings(q, b, b-k, b//2-ell)
                                      for k in range(defect_nullity+1))
            assert completions == formula_completions
            F_ell = sum((F(gaussian(q, 2*ell, k))*qpower(q, -k*(k+1)//2)/eta(q, k-ell)
                         for k in range(ell, 2*ell+1)), F(0))
            ratio = F(total_a*completions, formula_frames)
            assert ratio == alpha*F_ell
            assert (ratio < 1) == (defect_nullity == 0)
            assert (ratio > 1) == (defect_nullity > 0)
            likelihood_checked.add(residual)

    assert total_frames == formula_frames
    iid_kernel = [F(iid_kernel_counts[k], total_a) for k in range(b+1)]
    frame_kernel = [F(frame_kernel_counts[k], total_frames) for k in range(b+1)]
    defect = [F(defect_counts[k], total_a) for k in range(b+1)]
    frame_defect = [F(frame_defect_counts[k], total_frames) for k in range(b+1)]
    for law in (iid_kernel, frame_kernel, defect, frame_defect):
        assert sum(law) == 1

    full_tv = sum((multiplicity*abs(F(count, total_frames)-F(1, total_a))
                   for count, multiplicity in completion_hist.items()), F(0))/2
    rank_tv = tv(frame_kernel, iid_kernel)
    assert full_tv == (1-alpha)*defect[0]
    assert full_tv == tv(frame_defect, defect)

    # Moment laws predicted by the general rectangular theory.
    predicted_mu, predicted_mu0, predicted_nu, predicted_nu0 = [], [], [], []
    for j in range(b+1):
        mu, nu = F(0), F(0)
        for s in range(j//2+1):
            number = subspace_type_count(q, b, j, s)
            if not number:
                continue
            mu += F(number*embeddings(q, b, j, s), embeddings(q, a+b, j, s))
            nu += number*embeddings(q, a, j, s)*qpower(q, -a*j-j*(b-j))
        predicted_mu.append(mu)
        predicted_mu0.append(gaussian(q, b, j)*qpower(q, -a*j))
        predicted_nu.append(nu)
        predicted_nu0.append(gaussian(q, b, j)*qpower(q, -b*j+j*(j+1)//2))
    assert gaussian_moments(q, frame_kernel) == predicted_mu
    assert gaussian_moments(q, iid_kernel) == predicted_mu0
    assert gaussian_moments(q, defect) == predicted_nu
    assert invert_gaussian_moments(q, predicted_mu) == frame_kernel
    assert invert_gaussian_moments(q, predicted_nu) == defect

    # Independent enumeration of every alternating b-by-b matrix.
    alt_counts = Counter()
    D = b*(b-1)//2
    for triangle in product(range(q), repeat=D):
        alt_counts[b-field.rank(field.alternating_matrix(triangle, b), b, b)] += 1
    alternating = [F(alt_counts[k], q**D) for k in range(b+1)]
    assert gaussian_moments(q, alternating) == predicted_nu0
    assert invert_gaussian_moments(q, predicted_nu0) == alternating

    # Verify the averaged Phi moment identities directly by enumerating Alt_j.
    # This is a separate algebraic check of their normalization and powers of q.
    for j in range(b+1):
        sum_mu, sum_nu = F(0), F(0)
        Dj = j*(j-1)//2
        for triangle in product(range(q), repeat=Dj):
            rank = field.rank(field.alternating_matrix(triangle, j), j, j)
            s = rank//2
            def phi(dim):
                exponent = dim*j-j*(j-1)//2
                return F(embeddings(q, dim, j, s))*qpower(q, -exponent)
            phib, phia, phiab = phi(b), phi(a), phi(a+b)
            sum_mu += phib*phib/phiab
            sum_nu += phib*phia
        gammaj = F(gl_order(q, j), q**(j*j))
        mdj = qpower(q, -j*(j+a-b))/gammaj
        mprimej = qpower(q, -j*(j-1)//2)/gammaj
        assert mdj*sum_mu/q**Dj == predicted_mu[j]
        assert mprimej*sum_nu/q**Dj == predicted_nu[j]

    return {
        "q": q, "a": a, "b": b,
        "field": "GF(2)[x]/(x^2+x+1)" if q == 4 else f"GF({q})",
        "A_matrices_enumerated": total_a,
        "B_matrices_enumerated": q**(b*b),
        "all_pairs_counted_by_gram_grouping": total_a*q**(b*b),
        "symplectic_frames_counted": total_frames,
        "distinct_residual_matrices_checked": len(likelihood_checked),
        "alpha": str(alpha),
        "full_matrix_TV": str(full_tv),
        "rank_TV": str(rank_tv),
        "iid_defect_vs_uniform_alternating_TV": str(tv(defect, alternating)),
        "iid_kernel_law": stringify(iid_kernel),
        "frame_kernel_law": stringify(frame_kernel),
        "iid_defect_nullity_law": stringify(defect),
        "frame_defect_nullity_law": stringify(frame_defect),
        "uniform_alternating_nullity_law": stringify(alternating),
        "frame_kernel_gaussian_moments": stringify(predicted_mu),
        "iid_defect_gaussian_moments": stringify(predicted_nu),
        "all_exact_checks_passed": True,
    }


def main():
    cases = [(2,2,2), (2,4,2), (2,6,2), (3,2,2), (4,2,2), (2,4,4), (3,4,2), (4,4,2)]
    records = []
    for case in cases:
        result = run_case(*case)
        records.append(result)
        print(f"PASS q={case[0]}, a={case[1]}, b={case[2]}: "
              f"full TV={result['full_matrix_TV']}, rank TV={result['rank_TV']}; "
              f"{result['symplectic_frames_counted']} frames", flush=True)
    out = Path(__file__).resolve().parents[1] / 'results'
    out.mkdir(parents=True, exist_ok=True)
    (out/"exhaustive_results.json").write_text(json.dumps({
        "method": "Independent exhaustive A and B enumeration, grouped by exact alternating Gram matrix",
        "arithmetic": "Integer counts, exact rational probabilities, genuine GF4 arithmetic",
        "asymptotic_claims_checked": False,
        "cases": records,
        "all_checks_passed": all(r["all_exact_checks_passed"] for r in records),
    }, indent=2)+"\n")
    fields = ["q","a","b","A_matrices_enumerated","B_matrices_enumerated",
              "symplectic_frames_counted","full_matrix_TV","rank_TV",
              "iid_defect_vs_uniform_alternating_TV"]
    with (out/"exhaustive_summary.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)


if __name__ == "__main__":
    main()
