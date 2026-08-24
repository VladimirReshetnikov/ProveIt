"""Dense-capture check: can a negative cell be rescued by a dense higher-slice capturer
(M^{n+i'} >= A^{m+j}) under the exact B0/B1/B2 balances?

Prediction (Phi-contraction): B0 forces the negative coefficient to be so large that
even guaranteed dense capture V ~ M^{n+i'}/A^{m+j} cannot cover it: the requirement
c- <= c+ V, weighted by B0, telescopes to M^{n+i} >= A^{m+j'}, contradicting
admissibility.  So no dense-rescued pattern should survive the valuation-mass check.
"""
from fractions import Fraction
from itertools import combinations
import math

x = 14
M, A = 2**x + 6, 3**x + 2
ln2, ln3 = math.log(2), math.log(3)
lM, lA = x*ln2, x*ln3

def logMi(n,i): return (n+i)*lM
def logAj(m,j): return (m+j)*lA
def admissible(n,m,i,j):
    th = logMi(n,i)/logAj(m,j)
    return th < 1.0 and th > 7.0/12.0

def nullspace_exact(rows, q):
    mat = [[Fraction(v) for v in r] for r in rows]
    piv_cols, r = [], 0
    for c in range(q):
        piv = next((rr for rr in range(r, len(mat)) if mat[rr][c] != 0), None)
        if piv is None: continue
        mat[r], mat[piv] = mat[piv], mat[r]
        pv = mat[r][c]
        mat[r] = [v/pv for v in mat[r]]
        for rr in range(len(mat)):
            if rr != r and mat[rr][c] != 0:
                f = mat[rr][c]
                mat[rr] = [a - f*b for a,b in zip(mat[rr], mat[r])]
        piv_cols.append(c); r += 1
        if r == len(mat): break
    free = [c for c in range(q) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [Fraction(0)]*q
        v[fc] = Fraction(1)
        for ri, pc in enumerate(piv_cols):
            v[pc] = -mat[ri][fc]
        den = 1
        for a in v: den = den*a.denominator//math.gcd(den, a.denominator)
        vi = [int(a*den) for a in v]
        g = 0
        for a in vi: g = math.gcd(g, abs(a))
        if g: vi = [a//g for a in vi]
        basis.append(vi)
    return basis

def dense_over(n, m, i2, j2, j):
    """(i2,j2) dense over slice j: window length >= slice top."""
    return j2 > j and logMi(n, i2) >= logAj(m, j)

def analyze(n, m, D):
    cells = [(i,j) for i in range(D) for j in range(D) if admissible(n,m,i,j)]
    # dense pairs available on this grid?
    dense_pairs = [((i2,j2), j) for (i2,j2) in cells for j in range(D)
                   if any((i,j) in cells for i in range(D)) and dense_over(n,m,i2,j2,j)]
    print(f"[grid n={n} m={m} D={D}] {len(cells)} cells; dense (capturer, slice) pairs: {len(dense_pairs)}")
    rescued, tested = 0, 0
    examples = []
    for supp in combinations(cells, 5):
        rows = [[M**i * A**j for (i,j) in supp],
                [i * M**i * A**j for (i,j) in supp],
                [j * M**i * A**j for (i,j) in supp]]
        for v in nullspace_exact(rows, len(supp)):
            if all(a == 0 for a in v): continue
            tested += 1
            for sgn in (1,-1):
                c = {cell: sgn*a for cell,a in zip(supp,v) if a != 0}
                negs = [(k,val) for k,val in c.items() if val < 0]
                if not negs: continue
                for (i,j), val in negs:
                    # dense rescuers present for this negative?
                    dr = [(k,v2) for k,v2 in c.items() if v2 > 0 and dense_over(n,m,k[0],k[1],j)]
                    if not dr: continue
                    # exact dense-rescue mass test: c- <= sum c+ * ceil(M^{n+i2}/A^{m+j}) + slack
                    cap = sum(v2 * (2**( max(0, round(logMi(n,k[0]) - logAj(m,j))) if False else 0) +
                              int(math.exp(min(700, logMi(n,k[0]) - logAj(m,j)))) + 2)
                              for k,v2 in dr)
                    if cap >= -val:
                        rescued += 1
                        if len(examples) < 3:
                            examples.append((dict(c), (i,j)))
    print(f"  directions tested: {tested}; dense-rescued negatives surviving mass test: {rescued}")
    for c, negcell in examples:
        print(f"    example: neg {negcell}, pattern {c}")

for (n,m,D) in [(6,4,5), (10,7,5)]:
    analyze(n,m,D)
    print()
