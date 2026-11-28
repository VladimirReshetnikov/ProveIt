"""Independent exhaustive check of the four-statistic bilinear likelihood.

All comparisons are integer equalities.  NumPy is used only to enumerate finite
vectors and multiply matrices; formulas use Python integers throughout.
"""
from itertools import product
from collections import Counter
from fractions import Fraction
from math import comb, prod
import json
from pathlib import Path
import numpy as np


def gaussian(n, k, q):
    if not 0 <= k <= n:
        return 0
    return prod(q**(n-i)-1 for i in range(k)) // prod(q**(k-i)-1 for i in range(k))


def rank_mod(a, q):
    a = [list(map(int, row)) for row in a]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j] % q), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][j] % q, -1, q)
        a[r] = [(x * inv) % q for x in a[r]]
        for i in range(len(a)):
            if i != r:
                c = a[i][j]
                a[i] = [(x - c*y) % q for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def predicted_count(y, q, d):
    a, m = y.shape
    r = rank_mod(y, q)
    h = int(np.sum(np.all(y == 0, axis=1)))
    k = int(np.sum(np.all(y == 0, axis=0)))
    N = q**d
    out = 0
    for s in range(r, min(a, d)+1):
        superspaces = sum((-1)**j * comb(h, j) * gaussian(a-r-j, s-r, q) for j in range(h+1))
        assert superspaces >= 0
        out += superspaces * prod(N-q**i for i in range(s)) * (N//q**s-1)**k * (N//q**s)**(m-k)
    return out


def verify_case(q, d, a, m):
    vectors = np.array(list(product(range(q), repeat=d))[1:], dtype=np.int64)
    column_vectors = np.array(list(product(range(q), repeat=a)), dtype=np.int64)
    radix = q**a
    digits = q**np.arange(a-1, -1, -1, dtype=np.int64)
    counts = np.zeros(radix**m, dtype=np.int64)
    for idx in product(range(len(vectors)), repeat=a):
        anchors = vectors[list(idx)]
        columns = (anchors @ vectors.T) % q
        codes = digits @ columns
        column_counts = np.bincount(codes, minlength=radix)
        joint = column_counts
        for _ in range(1, m):
            joint = np.multiply.outer(joint, column_counts).reshape(-1)
        counts += joint
    signature_counts = Counter()
    tv_numerator = Fraction(0)
    N = q**d
    total = (N-1)**(a+m)
    q0 = Fraction(N-q, q*(N-1))
    q1 = Fraction(N, q*(N-1))
    for code, columns in enumerate(product(range(radix), repeat=m)):
        y = column_vectors[list(columns)].T
        expected = predicted_count(y, q, d)
        assert int(counts[code]) == expected, (q, d, a, m, y, int(counts[code]), expected)
        r = rank_mod(y, q)
        h = int(np.sum(np.all(y == 0, axis=1)))
        k = int(np.sum(np.all(y == 0, axis=0)))
        W = int(np.sum(y == 0))
        signature_counts[(r,h,k,W)] += 1
        tv_numerator += abs(Fraction(expected, total) - q0**W * q1**(a*m-W))
    assert sum(map(int, counts)) == total
    tv = tv_numerator/2
    return dict(q=q,d=d,a=a,m=m,latent_assignments=total,
                output_matrices=radix**m,statistic_classes=len(signature_counts),
                exact_tv=str(tv),tv=float(tv),all_integer_checks_passed=True)


if __name__ == '__main__':
    cases = [(2,2,2,2),(3,2,2,2),(2,2,3,2),(2,4,2,3),(2,4,3,3),(3,4,2,2)]
    results = [verify_case(*case) for case in cases]
    output = Path(__file__).with_name('independent_counts_results.json')
    output.write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps(results, indent=2))
