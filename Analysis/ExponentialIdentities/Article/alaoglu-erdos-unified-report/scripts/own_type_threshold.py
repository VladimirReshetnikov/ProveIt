"""A self-contained type threshold, independent of the quoted Pila constant 832.

Interpolation determinant with rows = L points of Sol cap [0,T] and columns
    phi_{i,j,k}(z) = 2^{iz} 3^{jz} g(z)^k,   i a + j b <= Lam,  0 <= k <= d.
All entries are INTEGERS on Sol, so a nonzero determinant has |Delta| >= 1, against the
Gelfond-type bound  |Delta| <= L! (T/R)^{L(L-1)/2} prod max|phi|,  R = cT.
Inputs from this corpus: the monoid density  #(Sol cap [0,T]) = T^2/(2 beta) + O(T), and
the greedy-support mean frequency (2/3) Lam.  Taking L = T^2/(2 beta) and
Lam^2 (d+1) = T^2 ab / beta, the contradiction reduces (after dividing by T^2) to

    log c / (4 beta)  >  (2c/3) sqrt(ab / (beta (d+1)))  +  tau c^2 d / 2 .

Optimising over c and d gives tau_crit = 1/(C beta^2 log2 log3) with C ~ 4570, and the
beta^-2 scaling is exact rather than fitted.
"""
import math

a, b = math.log(2), math.log(3)

def rhs(c, D, tau, beta):
    return (2 * c / 3) * math.sqrt(a * b / (beta * D)) + tau * c * c * (D - 1) / 2

def margin(tau, beta):
    best = -1e9
    for ci in range(1, 4000):
        c = 1.0 + ci * 0.05
        D = (2 * math.sqrt(a * b / beta) / (3 * tau * c)) ** (2.0 / 3.0)
        for Dt in (max(1.0, math.floor(D)), max(1.0, math.ceil(D)), max(1.0, D)):
            best = max(best, math.log(c) / (4 * beta) - rhs(c, Dt, tau, beta))
    return best

def tau_crit(beta):
    lo, hi = 1e-14, 1.0
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if margin(mid, beta) > 0:
            lo = mid
        else:
            hi = mid
    return lo

if __name__ == "__main__":
    print(f"{'beta':>6} {'tau_crit':>15} {'C = 1/(tau b^2 ab)':>20} {'Pila 1/(832 b^2 ab)':>21}")
    Cs = []
    for beta in (14, 20, 27, 50, 100):
        tc = tau_crit(beta)
        C = 1.0 / (tc * beta * beta * a * b)
        Cs.append(C)
        print(f"{beta:6} {tc:15.6e} {C:20.1f} {1.0/(832*beta*beta*a*b):21.6e}")
    C = sum(Cs) / len(Cs)
    print(f"\nC stable to {100*(max(Cs)-min(Cs))/C:.3f}%  ->  C = {C:.0f}  "
          f"({C/832:.2f}x more conservative than the quoted 832)")
    print(f"excess factor of the vanishing branch = C*ab/4 * beta = {C*a*b/4:.1f} * beta "
          f"(linear in beta for ANY constant)")
