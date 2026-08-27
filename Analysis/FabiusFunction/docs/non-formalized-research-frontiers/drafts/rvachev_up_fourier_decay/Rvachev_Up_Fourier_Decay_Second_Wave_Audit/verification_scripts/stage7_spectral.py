"""Stage 7: high-precision spectral verification of second-wave constants.

Adjudicates, at 40 working digits (mpmath), the constants claimed by the
second-wave documents (rvachev_up_fourier_decay-5..8):

  * rho_1   : Perron root of the q=1 transfer operator (Chebyshev-Lobatto
              collocation at N=48 and N=64, power iteration on M and M^T);
  * kappa_1 : 1/2 + log(pi/rho_1)/log 2;
  * A_1     : shell mean constant  (int h) * nu(W)  [Doc 5 eq (A1),
              Doc 6 eq (A1-numeric), Doc 7 eq (A1)];
  * B_1     : per-shell logarithmic mass  (int h) * nu(W/(1+.))  [Doc 5];
  * A_1^log : B_1/log 2  [Docs 5,6,7];
  * C_*     : exact peak-ray constant  |Phi(2^n * 2/3)| / E_{kappa_inf}(...),
              constant in n (Doc 6 eq (Cstar): 0.139129774734829);
  * rho_q   : q = 3, 4, 8, 16 collocation eigenvalues (Doc 6 sample spectrum);
  * the 19-20 digit constants of Doc 8's appendix, and Doc 7's variance
    check number Var(S_1000).

Writes constants.json for stage8_profile.py.

The eigen-normalisation used throughout: L h = rho h with nu(h) = 1, and the
discrete left eigenvector w of the collocation matrix is the atom-weight
vector of the discrete eigenmeasure: nu(phi) ~ (w . phi(nodes)) / (w . h).
A_1 = (int_0^1 h) * nu(W) where
  W(z) = (rho/pi) H(1+z) (1+z)^(kappa_1 - 1) exp(log^2(1+z)/(2 log 2)),
  H(y) = prod_{m>=1} |sinc(pi y / 2^m)|.
"""

import json
import os
from mpmath import mp, mpf, cos, sin, pi, log, exp, sqrt, matrix, power

mp.dps = 40

A = log(2)


# ----------------------------------------------------------------------
# Chebyshev-Lobatto collocation of (L_q f)(x)
#   = 1/2 [ sin^q(pi x/2) f(x/2) + cos^q(pi x/2) f((x+1)/2) ]
# ----------------------------------------------------------------------

def lobatto_nodes(N):
    return [(1 - cos(mpf(j) * pi / (N - 1))) / 2 for j in range(N)]


def bary_weights(N):
    w = []
    for j in range(N):
        wj = mpf(-1) ** j
        if j == 0 or j == N - 1:
            wj /= 2
        w.append(wj)
    return w


def bary_row(t, nodes, w):
    """Row of barycentric interpolation weights evaluated at point t."""
    N = len(nodes)
    for j in range(N):
        if t == nodes[j]:
            return [mpf(1) if i == j else mpf(0) for i in range(N)]
    terms = [w[j] / (t - nodes[j]) for j in range(N)]
    s = sum(terms)
    return [tj / s for tj in terms]


def transfer_matrix(N, q):
    nodes = lobatto_nodes(N)
    w = bary_weights(N)
    M = matrix(N, N)
    for i in range(N):
        x = nodes[i]
        sw = sin(pi * x / 2) ** q / 2
        cw = cos(pi * x / 2) ** q / 2
        r0 = bary_row(x / 2, nodes, w)
        r1 = bary_row((x + 1) / 2, nodes, w)
        for j in range(N):
            M[i, j] = sw * r0[j] + cw * r1[j]
    return M, nodes


def power_iter(M, iters=260, transpose=False):
    N = M.rows
    v = matrix([mpf(1)] * N)
    for _ in range(iters):
        v = (M.T * v) if transpose else (M * v)
        nrm = max(abs(x) for x in v)
        v = v / nrm
    return v


def leading_triple(N, q):
    """(rho, right eigvec at nodes, left eigvec, nodes)."""
    M, nodes = transfer_matrix(N, q)
    v = power_iter(M)
    w = power_iter(M, transpose=True)
    Mv = M * v
    num = sum(w[i] * Mv[i] for i in range(N))
    den = sum(w[i] * v[i] for i in range(N))
    return num / den, v, w, nodes


# ----------------------------------------------------------------------
# Clenshaw-Curtis integration on the same Lobatto nodes (interval [0,1])
# via Chebyshev coefficients: values -> coeffs (DCT-I with halved ends),
# int_{-1}^{1} f = sum_{k even} 2 a_k / (1 - k^2); map to [0,1] gives x1/2.
# ----------------------------------------------------------------------

def cc_integrate(vals):
    N = len(vals)
    n = N - 1
    # node j here corresponds to theta_j = j*pi/n with x = (1 - cos theta)/2,
    # i.e. Chebyshev abscissa c_j = cos(theta_j) runs 1 -> -1 as j runs 0 -> n.
    total = mpf(0)
    for k in range(0, n + 1, 2):
        # a_k = (2/n) * sum'' vals_j cos(k j pi / n)
        s = mpf(0)
        for j in range(n + 1):
            term = vals[j] * cos(mpf(k * j) * pi / n)
            if j == 0 or j == n:
                term /= 2
            s += term
        a_k = 2 * s / n
        if k == 0:
            total += a_k  # 2*a0/(1-0) with a0 halved convention -> handle below
        else:
            total += 2 * a_k / (1 - k * k)
    # With the plain (non-halved a_0) convention above, int_{-1}^1 = a_0 + ...
    # where the k=0 contribution should be 2*a_0/2 = a_0: already added.
    return total / 2  # map [-1,1] -> [0,1]


def cc_selftest():
    N = 48
    nodes = lobatto_nodes(N)
    one = [mpf(1) for _ in nodes]
    sq = [x ** 2 for x in nodes]
    quartic = [x ** 4 for x in nodes]
    assert abs(cc_integrate(one) - 1) < mpf(10) ** (-35)
    assert abs(cc_integrate(sq) - mpf(1) / 3) < mpf(10) ** (-35)
    assert abs(cc_integrate(quartic) - mpf(1) / 5) < mpf(10) ** (-35)


# ----------------------------------------------------------------------
# The sinc tail H and the shell weight W
# ----------------------------------------------------------------------

def H_tail(y, mmax=140):
    """H(y) = prod_{m>=1} |sinc(pi y / 2^m)| for 1 <= y < 2."""
    s = mpf(0)
    for m in range(1, mmax + 1):
        u = pi * y / 2 ** m
        s += log(abs(sin(u) / u))
    return exp(s)


def W_weight(z, rho, kappa1):
    y = 1 + z
    return (rho / pi) * H_tail(y) * y ** (kappa1 - 1) * exp(log(y) ** 2 / (2 * A))


# ----------------------------------------------------------------------
# Direct evaluation of Phi(x) = prod_{h>=0} sinc(pi x / 2^h)
# ----------------------------------------------------------------------

def Phi(x, extra=140):
    hmax = int(mp.log(x, 2)) + extra if x > 1 else extra
    s = mpf(0)
    for h in range(hmax + 1):
        u = pi * x / 2 ** h
        s += log(abs(sin(u) / u))
    return exp(s)


def E_kappa(x, kappa):
    return x ** (-kappa) * exp(-log(x) ** 2 / (2 * A))


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    cc_selftest()
    out = {}

    print("=" * 72)
    print("q = 1 Perron data (N = 48 and N = 64 collocation, dps = 40)")
    print("=" * 72)
    results = {}
    for N in (48, 64):
        rho, v, w, nodes = leading_triple(N, 1)
        kappa1 = mpf(1) / 2 + log(pi / rho) / A
        int_h = cc_integrate([v[i] for i in range(N)])
        wh = sum(w[i] * v[i] for i in range(N))
        Wvals = [W_weight(nodes[i], rho, kappa1) for i in range(N)]
        nuW = sum(w[i] * Wvals[i] for i in range(N)) / wh
        nuWlog = sum(w[i] * Wvals[i] / (1 + nodes[i]) for i in range(N)) / wh
        A1 = int_h * nuW
        B1 = int_h * nuWlog
        results[N] = (rho, kappa1, A1, B1)
        print(f"N={N}:  rho_1    = {mp.nstr(rho, 30)}")
        print(f"        kappa_1  = {mp.nstr(kappa1, 30)}")
        print(f"        A_1      = {mp.nstr(A1, 24)}")
        print(f"        B_1      = {mp.nstr(B1, 24)}")
        print(f"        A_1^log  = {mp.nstr(B1 / A, 24)}")

    rho48, kappa48, A1_48, B1_48 = results[48]
    rho64, kappa64, A1_64, B1_64 = results[64]
    print(f"\n|rho(48) - rho(64)|   = {mp.nstr(abs(rho48 - rho64), 3)}")
    print(f"|A_1(48) - A_1(64)|   = {mp.nstr(abs(A1_48 - A1_64), 3)}")
    print(f"|B_1(48) - B_1(64)|   = {mp.nstr(abs(B1_48 - B1_64), 3)}")

    out["rho1"] = mp.nstr(rho64, 32)
    out["kappa1"] = mp.nstr(kappa64, 32)
    out["A1_spectral"] = mp.nstr(A1_64, 26)
    out["B1_spectral"] = mp.nstr(B1_64, 26)
    out["A1log_spectral"] = mp.nstr(B1_64 / A, 26)

    print()
    print("Claimed values:")
    print("  Doc 5      A_1 = 0.0912661241315...")
    print("  Doc 6/7    A_1 = 0.091266124131588... / 0.09126612413159...")
    print("  Doc 5      B_1 = 0.065059235040389...")
    print("  Doc 5      A_1^log = 0.0938606357568 / B_1/a = 0.093860635756799")
    print("  Doc 6      A_1^log = 0.09386063575678...")
    print("  Doc 7      A_1^log = 0.09386063575679... (direct: ...78312)")

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("Exact peak ray x = 2^n * (2/3): C_* and constancy (Doc 6)")
    print("=" * 72)
    kappa_inf = mpf(3) / 2 + log(pi / sqrt(3)) / A
    cstars = []
    for n in (0, 5, 10, 15):
        x = mpf(2) ** n * mpf(2) / 3
        cst = Phi(x) / E_kappa(x, kappa_inf)
        cstars.append(cst)
        print(f"n={n:2d}:  |Phi|/E_kappa_inf = {mp.nstr(cst, 25)}")
    spread = max(cstars) - min(cstars)
    print(f"max spread over n     = {mp.nstr(spread, 3)}")
    print("claimed C_* (Doc 6)   = 0.139129774734829...")
    out["Cstar"] = mp.nstr(cstars[-1], 26)
    out["kappa_inf"] = mp.nstr(kappa_inf, 32)

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("q-spectrum rho_q, kappa_q for q = 3, 4, 8, 16 (Doc 6 table)")
    print("=" * 72)
    claimed = {3: ("0.3948966324", "2.5983138062"),
               4: ("0.3201941016", "2.5622414703"),
               8: ("0.1612444589", "2.4805809434"),
               16: ("0.0500719357", "2.4214870020")}
    out_q = {}
    for q in (3, 4, 8, 16):
        rho_q, _, _, _ = leading_triple(48, q)
        Lam = power(rho_q, mpf(1) / q)
        kq = (log(pi) + A / 2 - log(Lam)) / A
        out_q[q] = (mp.nstr(rho_q, 16), mp.nstr(kq, 16))
        print(f"q={q:2d}: rho_q = {mp.nstr(rho_q, 14)}  (claimed {claimed[q][0]})")
        print(f"       kappa_q = {mp.nstr(kq, 14)}  (claimed {claimed[q][1]})")
    out["q_spectrum"] = out_q

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("rho_1 collocation convergence (Doc 6 table, N = 8..24)")
    print("=" * 72)
    doc6_table = {8: "0.661322639955074", 10: "0.661322602233874",
                  12: "0.661322602061258", 16: "0.661322602060566",
                  24: "0.661322602060565"}
    for N in (8, 10, 12, 16, 24):
        rho_N, _, _, _ = leading_triple(N, 1)
        print(f"N={N:2d}: {mp.nstr(rho_N, 16)}   (Doc 6: {doc6_table[N]})")

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("Doc 8 appendix constants (19-20 digits) and misc checks")
    print("=" * 72)
    beta = log(sqrt(3) / 2)
    c_lam = (A / pi) * sqrt(mpf(3) / 2)
    kappa0 = mpf(3) / 2 + log(pi) / A
    kappa2 = log(2 * pi) / A
    combo = A / 2 + log(pi) - beta
    print(f"a       = {mp.nstr(A, 20)}   (claimed 0.6931471805599453094)")
    print(f"beta    = {mp.nstr(beta, 20)}   (claimed -0.1438410362258904637)")
    print(f"c       = {mp.nstr(c_lam, 20)}   (claimed 0.2702223197333653409)")
    print(f"a/2+log pi-beta = {mp.nstr(combo, 20)}  (claimed 1.6351445123552632926)")
    print(f"kappa_0 = {mp.nstr(kappa0, 20)}   (claimed 3.1514961294723187980)")
    print(f"kappa_1 = {mp.nstr(kappa64, 20)}   (claimed 2.7480700148713340157)")
    print(f"kappa_2 = {mp.nstr(kappa2, 20)}   (claimed 2.6514961294723187980)")
    print(f"kappa_inf = {mp.nstr(kappa_inf, 20)} (claimed 2.3590148791117407073)")

    var1000 = pi ** 2 / 4 * 1000 - pi ** 2 / 3 * (1 - mpf(2) ** (-1000))
    print(f"Var(S_1000) = {mp.nstr(var1000, 15)}   (Doc 7: 2464.1112321386)")

    # int_0^{pi/2} log^2 tan u du = pi^3 / 8  (Doc 6's d-variance integral)
    val = mp.quad(lambda u: log(mp.tan(u)) ** 2, [0, pi / 4, pi / 2])
    print(f"int_0^(pi/2) log^2 tan = {mp.nstr(val, 20)}  vs pi^3/8 = "
          f"{mp.nstr(pi ** 3 / 8, 20)}")

    out["beta"] = mp.nstr(beta, 26)
    out["c_lambert"] = mp.nstr(c_lam, 26)
    out["kappa0"] = mp.nstr(kappa0, 32)
    out["kappa2"] = mp.nstr(kappa2, 32)

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "constants.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("\nconstants.json written.")


if __name__ == "__main__":
    main()
