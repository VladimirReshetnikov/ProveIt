"""2D sign-pattern feasibility: exact balances vs tail-sum and coverage constraints.

Cells (i,j) on a truncated admissible grid carry G_{i,j} = (A^{m+j}) falling (M^{n+i}),
M = 2^x, A = 3^x, x = 14 (exact integers).  A viable integrality candidate c must satisfy
  (B0) sum c_ij M^i A^j = 0
  (B1) sum i c_ij M^i A^j = 0
  (B2) sum j c_ij M^i A^j = 0        [the vector derivative cancellation]
plus, from the exact top-slice tail-sum rigidity: all tail sums of the top slice >= 0;
plus, for every negative cell, the coverage necessity (window primes must be capturable).

We compute the exact integer nullspace of (B0,B1,B2) restricted to small supports and
test every nullspace direction (up to sign) against the two structural constraints.
"""
from fractions import Fraction
from itertools import combinations
import math

x = 14
M, A = 2**x + 6, 3**x + 2   # perturbed generic pair: multiplicatively independent,
                            # same size profile, no control relations
ln2, ln3 = math.log(2), math.log(3)
lM, lA = x*ln2, x*ln3

def logMi(n,i): return (n+i)*lM
def logAj(m,j): return (m+j)*lA
def admissible(n,m,i,j):
    th = logMi(n,i)/logAj(m,j)
    return th < 1.0 and th > 7.0/12.0   # window nonempty + Huxley

def nullspace_exact(rows, q):
    """Exact rational nullspace of a small integer matrix (list of rows, q columns)."""
    mat = [[Fraction(v) for v in r] for r in rows]
    ncols = q
    piv_cols = []
    r = 0
    for c in range(ncols):
        piv = None
        for rr in range(r, len(mat)):
            if mat[rr][c] != 0:
                piv = rr; break
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
    free = [c for c in range(ncols) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [Fraction(0)]*ncols
        v[fc] = Fraction(1)
        for ri, pc in enumerate(piv_cols):
            v[pc] = -mat[ri][fc]
        # clear denominators -> integer vector
        den = 1
        for a in v: den = den*a.denominator//math.gcd(den, a.denominator)
        vi = [int(a*den) for a in v]
        g = 0
        for a in vi: g = math.gcd(g, abs(a))
        if g: vi = [a//g for a in vi]
        basis.append(vi)
    return basis

def s_digits(nn, b):
    t = 0
    while nn:
        t += nn % b
        nn //= b
    return t

def v2_desc(N, K):
    # v_2((N)_K) = K + s_2(N-K) - s_2(N)  (Legendre)
    return K + s_digits(N-K, 2) - s_digits(N, 2)

def v3_desc(N, K):
    return (K + s_digits(N-K, 3) - s_digits(N, 3)) // 2

def analyze(n, m, D, max_support=6, verbose_limit=4):
    cells = [(i,j) for i in range(D) for j in range(D) if admissible(n,m,i,j)]
    print(f"[grid n={n} m={m} D={D}] {len(cells)} admissible cells")
    survivors = []
    tested = 0
    for supp in combinations(cells, max_support):
        # need nullity: 3 equations, q columns -> expect q-3 dims; take q=4,5,6
        rows = [[M**i * A**j for (i,j) in supp],
                [i * M**i * A**j for (i,j) in supp],
                [j * M**i * A**j for (i,j) in supp]]
        basis = nullspace_exact(rows, len(supp))
        for v in basis:
            tested += 1
            if all(a == 0 for a in v): continue
            for sgn in (1, -1):
                c = {cell: sgn*a for cell, a in zip(supp, v) if a != 0}
                if not c: continue
                if not any(val < 0 for val in c.values()): continue
                # ALL-SLICE tail-sum constraint (Theorem A hypothesis)
                ok = True
                for jj in sorted({j for (_, j) in c}):
                    slice_cells = sorted([(i,j) for (i,j) in c if j == jj])
                    for k in range(len(slice_cells)):
                        t = sum(c[cell] for cell in slice_cells[k:])
                        if t < 0: ok = False; break
                    if not ok: break
                if not ok: continue
                # coverage necessity for every negative cell
                for (i,j), val in c.items():
                    if val >= 0: continue
                    log_primes = logMi(n,i) - math.log(logAj(m,j))
                    caplogs = []
                    for (i2,j2), v2 in c.items():
                        if v2 <= 0 or j2 < j or (i2,j2)==(i,j): continue
                        if j2 == j:
                            caplogs.append(min(logMi(n,i), logMi(n,i2))
                                           - math.log(logAj(m,j)))
                        else:
                            caplogs.append(logMi(n,i2)
                                           + math.log((m+j2)/(m+j)))
                    if not caplogs: ok = False; break
                    tot = max(caplogs) + math.log(len(caplogs))
                    if tot < log_primes: ok = False; break
                    # valuation-mass necessity: c^- * #primes <= sum c^+ * incidence
                    lhs = math.log(-val) + log_primes
                    rhs_terms = []
                    for (i2,j2), v2 in c.items():
                        if v2 <= 0 or j2 < j or (i2,j2)==(i,j): continue
                        if j2 == j:
                            inc = min(logMi(n,i), logMi(n,i2)) - math.log(logAj(m,j))
                        else:
                            inc = logMi(n,i2) + math.log((m+j2)/(m+j))
                        rhs_terms.append(math.log(v2) + inc)
                    rhs = max(rhs_terms) + math.log(len(rhs_terms))
                    if rhs < lhs: ok = False; break
                if ok:
                    # exact structural-prime constraints v_2, v_3 >= 0
                    v2 = sum(val * v2_desc(A**(m+j2), M**(n+i2))
                             for (i2,j2), val in c.items())
                    v3 = sum(val * v3_desc(A**(m+j2), M**(n+i2))
                             for (i2,j2), val in c.items())
                    if v2 < 0 or v3 < 0: continue
                    survivors.append((supp, dict(c)))
    print(f"  nullspace directions tested: {tested}; surviving sign patterns: {len(survivors)}")
    for supp, c in survivors[:verbose_limit]:
        neg = sorted([k for k,v in c.items() if v<0]); pos = sorted([k for k,v in c.items() if v>0])
        print(f"    survivor: neg cells {neg}, pos cells {pos}, coeffs {c}")
    return survivors

for (n,m,D) in [(6,4,4), (10,7,4), (6,4,5)]:
    analyze(n, m, D)
    print()
