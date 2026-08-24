"""Certified near-curve trap search on dyadic blocks.

Block L: integer points (X, Y) with 2^L <= X < 2^{L+1} and Y = X^theta, theta = log_2 3.
Normalising z = X/2^L in [1,2] and Y/3^L = z^theta, a polynomial P = sum c_ij X^i Y^j
restricts to the curve as

    F(z) = sum_{(i,j) in S} c_ij * 2^{Li} 3^{Lj} * z^{i + j theta} .

If sup_{z in [1,2]} |F(z)| < 1 then every integer curve point of the block is a zero of P
(an integer of modulus < 1 vanishes), and by the fewnomial/Chebyshev bound P has at most
|S| - 1 zeros on the curve -- so a counterexample with generator x forces
|S| - 1 >= ceil((L+1)/x).  Certified covers of total defect o(L) would PROVE the conjecture.

Method: expand each basis function phi_ij(z) = 2^{Li} 3^{Lj} z^{i+j theta} in Chebyshev
polynomials on [1,2] to N terms at high precision, build the integer lattice
    rows = [ e_ij | round(scale * cheb_k(phi_ij)) ]
and LLL-reduce.  A short vector gives a candidate coefficient vector c; the true sup is
then measured directly at high precision on a fine grid (the reported sup is a measurement,
not a proof -- a rigorous certificate needs directed rounding, flagged in the output).
"""
import math
from mpmath import mp, mpf, chebyfit, log

mp.dps = 60

THETA = log(3) / log(2)


def basis(L, S, N):
    """Chebyshev coefficients on [1,2] of phi_ij for each (i,j) in S."""
    rows = []
    for (i, j) in S:
        w = mpf(2) ** (L * i) * mpf(3) ** (L * j)
        lam = mpf(i) + mpf(j) * THETA
        f = lambda z, w=w, lam=lam: w * (z ** lam)
        co = chebyfit(f, [mpf(1), mpf(2)], N)
        rows.append([mpf(c) for c in co])
    return rows


def lll_short(rows, S, scale):
    """LLL on [ identity | round(scale * cheb) ] and return the candidate coefficient vectors."""
    from sympy import Matrix, ZZ
    from sympy.polys.matrices import DomainMatrix
    n = len(S)
    N = len(rows[0])
    M = []
    for idx in range(n):
        coeff = [0] * n
        coeff[idx] = 1
        tail = [int(mp.nint(scale * rows[idx][k])) for k in range(N)]
        M.append(coeff + tail)
    dm = DomainMatrix.from_Matrix(Matrix(M)).convert_to(ZZ)
    red = dm.lll().to_Matrix()
    out = []
    for r in range(red.rows):
        c = [int(red[r, k]) for k in range(n)]
        if any(c):
            out.append(c)
    return out


def sup_on_block(L, S, c, pts=400):
    """Measured sup of |F| on [1,2] at high precision."""
    best = mpf(0)
    for t in range(pts + 1):
        z = mpf(1) + mpf(t) / pts
        v = mpf(0)
        for (i, j), ci in zip(S, c):
            if ci:
                v += ci * (mpf(2) ** (L * i)) * (mpf(3) ** (L * j)) * (z ** (mpf(i) + mpf(j) * THETA))
        best = max(best, abs(v))
    return best


def support(d):
    return [(i, j) for i in range(d + 1) for j in range(d + 1 - i)]


if __name__ == "__main__":
    print("Certified near-curve trap search (measured sup; rigorous certificate needs")
    print("directed rounding -- see module docstring).\n")
    print(f"{'L':>4} {'d':>3} {'|S|':>5} {'best measured sup':>22} {'subunit?':>10}")
    for L in (1, 2, 3, 4, 6, 8):
        found = False
        for d in (2, 3, 4, 5, 6):
            S = support(d)
            N = min(3 * len(S) + 6, 40)
            try:
                rows = basis(L, S, N)
            except Exception as e:
                print(f"{L:4} {d:3} {len(S):5}   basis failed: {e}")
                continue
            mx = max(max(abs(x) for x in r) for r in rows)
            scale = mpf(10) ** 25 / mx if mx > 0 else mpf(1)
            try:
                cands = lll_short(rows, S, scale)
            except Exception as e:
                print(f"{L:4} {d:3} {len(S):5}   lll failed: {e}")
                continue
            best = None
            for c in cands[:6]:
                s = sup_on_block(L, S, c)
                if best is None or s < best:
                    best = s
            print(f"{L:4} {d:3} {len(S):5} {mp.nstr(best, 8):>22} {'YES' if best < 1 else 'no':>10}")
            if best is not None and best < 1:
                found = True
                break
        if not found:
            print(f"{L:4}   -- no subunit certificate found at these degrees")
