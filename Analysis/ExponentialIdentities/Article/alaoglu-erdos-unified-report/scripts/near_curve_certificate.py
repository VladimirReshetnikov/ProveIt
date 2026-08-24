"""Rigorous near-curve subunit certificates for y = x^(log_2 3), Brisebarre-Hanrot style.

=========================  WHAT IS PROVED  ==================================

Integer points of the curve  Y = X^theta,  theta = log_2 3,  are exactly the pairs
(2^t, 3^t) with t in Sol = {t >= 0 : 2^t and 3^t are both integers}.  Writing t for
log_2 X, a polynomial  P = sum_{(i,j) in S} c_ij X^i Y^j  with c_ij in Z restricts to
the curve as

        F(t)  =  P(2^t, 3^t)  =  sum_{(i,j) in S} c_ij exp(lambda_ij t),
        lambda_ij = i log 2 + j log 3.

SUBUNIT LOCKING.  If sup_{t in B} |F(t)| < 1 on a block B = [t0, t0+delta], then every
integer curve point with log_2 X in B is a zero of P (an integer of modulus < 1 is 0).
FEWNOMIAL BUDGET.  The exponents lambda_ij are pairwise distinct (2 and 3 are
multiplicatively independent), so {exp(lambda t)} is a Chebyshev system and a nonzero F
has at most |S| - 1 real zeros.  Hence B carries at most |S| - 1 points of Sol.
The DEFECT of the certificate is |S| - 1; the CAPACITY of a certified cover of a block is
the sum of the defects of its pieces.  Under a counterexample with least generator beta,
Sol = N_0 + N_0 beta forces at least ceil((t0+delta)/beta) points in [t0, t0+delta], so
certified covers of capacity o(L) along an unbounded sequence of unit blocks [L, L+1)
would PROVE the Alaoglu-Erdos statement.

THE CERTIFICATE.  Put c0 = t0 + delta/2, h = delta/2, t = c0 + h w with w in [-1,1].  Then
exp(lambda t) = W * exp(y w) with W = exp(lambda c0), y = lambda h, and the Bessel-Chebyshev
(Jacobi-Anger) expansion is exact:

        exp(y w) = I_0(y) + 2 sum_{n>=1} I_n(y) T_n(w),        |T_n(w)| <= 1.

Therefore, with A_n(c) = sum_e c_e W_e kappa_{n,e}, kappa_{0,e} = I_0(y_e) and
kappa_{n,e} = 2 I_n(y_e) for n >= 1,

        sup_{t in B} |F(t)|  <=  sum_{n<N} |A_n(c)|  +  sum_e |c_e| W_e tau_e(N),
        tau_e(N) := 2 sum_{n>=N} I_n(y_e)
                 <= 2 I_0(y_e) (y_e/2)^N / N! * 1/(1 - y_e/(2(N+1)))     [needs N+1 > y_e/2],

using I_n(y) <= (y/2)^n I_0(y)/n!, which follows from (n+k)! >= n! k! in the series
I_n(y) = sum_k (y/2)^(n+2k)/(k!(n+k)!).  These are the EXPLICIT TAIL COLUMNS: they are part
of the lattice, so the short vector is short for a bound that already includes truncation.

Every quantity on the right is evaluated as an ARB BALL (python-flint / Arb), i.e. with
rigorous directed-rounding enclosures, and the number returned is that ball's exact upper
endpoint.  A reported bound b < 1 is therefore a PROOF that sup_B |F| <= b < 1, hence a
PROOF that the block carries at most |S| - 1 points of Sol.  arb comparison has
"certainly" semantics -- a ball straddling 1 compares False both ways -- so the test
cannot report success on an inconclusive enclosure.

For extra tightness the bound is applied on Ksub equal sub-blocks of B and the maximum
taken; that is still a rigorous bound for B, and it converges to the true sup as Ksub grows.

=========================  WHAT IS ONLY MEASURED  ===========================

* The SEARCH for the integer vector c is heuristic: the rows W_e kappa_{n,e} and the tail
  weights W_e tau_e are scaled by 2^logsigma, rounded to integers, and LLL-reduced
  (flint fmpz_mat.lll).  Rounding inside the lattice is irrelevant to correctness, because
  the candidate c that comes out is re-certified from scratch with arb balls.
* Consequently every q_min in the tables is an UPPER BOUND for the true minimal support
  size: it is the smallest |S| at which THIS search found a certificate.  Nothing here
  shows that smaller supports admit none.
* The covolume "capacity index" log(covol)/q + log sqrt(gamma_q) is a Minkowski-type
  PREDICTION, not a bound on what LLL finds; it is used only to rank support shapes.
* Fitted growth laws are empirical fits over the reachable range, not theorems.

=========================  CONTROL CHECK  ==================================

The certificate half of this route (subunit locking + fewnomial budget) is completely
control-blind: it uses only multiplicative independence of 2 and 3, and holds verbatim at
the integer controls (M,A) = (2^m, 3^m).  The conditional input sits entirely in the other
half, the orbit pressure ceil((L+1)/beta), which is exactly hypothesis (ii) of the corpus
control principle (the exact least-generator monoid Sol = N_0 + N_0 beta).  At a control
Sol = N_0, the block [L,L+1) carries a single point, the criterion would need |S| - 1 < 1,
i.e. a monomial certificate |c| 2^{iL} 3^{jL} < 1, which is impossible for L >= 0 -- so the
route correctly yields no contradiction at controls.  The route is control-clean, and it
can only ever win on a RATE (capacity o(L)), never on structure.

Usage:
    python near_curve_certificate.py sweep  1 2 3 ...   # min |S| per unit block L
    python near_curve_certificate.py verify             # re-verify the stored certificates
    python near_curve_certificate.py shapes L q         # sparse vs dense support comparison
    python near_curve_certificate.py cover  L           # single block vs K-piece covers
    python near_curve_certificate.py long   L           # blocks of length delta = 1,2,4,8
"""
import sys, os, math, json, time, random, itertools
from fractions import Fraction
from flint import fmpz_mat, arb, ctx

LOG2, LOG3 = math.log(2), math.log(3)
lam_f = lambda p: p[0]*LOG2 + p[1]*LOG3


def to_int(x):
    return int(arb(x.mid()).floor().unique_fmpz())


# --------------------------------------------------------------------------
#  rigorous Bessel-Chebyshev rows
# --------------------------------------------------------------------------
_ROWS = {}


def cheb_rows(c0, h, S, N, prec):
    """c0, h : Fraction.  Block [c0-h, c0+h].  Returns arb balls (W_e, kappa[e][n], tau_e)
    with the guarantees stated in the module docstring."""
    key = (c0, h, tuple(S), N, prec)
    if key in _ROWS:
        return _ROWS[key]
    old = ctx.prec
    ctx.prec = prec
    try:
        l2, l3 = arb(2).log(), arb(3).log()
        C0 = arb(c0.numerator)/c0.denominator
        H = arb(h.numerator)/h.denominator
        W, K, T = [], [], []
        for (i, j) in S:
            lam = i*l2 + j*l3
            y = lam*H
            W.append((lam*C0).exp())
            K.append([y.bessel_i(0)] + [2*y.bessel_i(n) for n in range(1, N)])
            hh = y/2
            if not ((hh/(N + 1)).upper() < 0.5):
                raise ValueError("N too small for the tail bound")
            T.append(2*y.bessel_i(0)*(hh**N)/arb.fac_ui(N)/(1 - hh/(N + 1)))
        _ROWS[key] = (W, K, T)
        return W, K, T
    finally:
        ctx.prec = old


def _block_bound(c0, h, S, c, N, prec):
    old = ctx.prec
    ctx.prec = prec
    try:
        W, K, T = cheb_rows(c0, h, S, N, prec)
        tot = arb(0)
        for n in range(N):
            A = arb(0)
            for e in range(len(S)):
                if c[e]:
                    A += c[e]*W[e]*K[e][n]
            tot += arb(A.abs_upper())
        for e in range(len(S)):
            if c[e]:
                tot += abs(c[e])*W[e]*T[e]
        return arb(tot.upper())
    finally:
        ctx.prec = old


def _bound_family(c0, h, S, C, N, prec):
    """Rigorous bounds on the block [c0-h, c0+h] for a whole family of integer coefficient
    vectors at once (C is a list of lists).  Same bound as _block_bound, matrix form."""
    from flint import arb_mat
    old = ctx.prec
    ctx.prec = prec
    try:
        W, K, T = cheb_rows(c0, h, S, N, prec)
        q = len(S)
        A = arb_mat([[W[e]*K[e][n] for n in range(N)] for e in range(q)])
        Tv = arb_mat([[W[e]*T[e]] for e in range(q)])
        Cm = arb_mat([[arb(int(x)) for x in v] for v in C])
        Am = arb_mat([[arb(abs(int(x))) for x in v] for v in C])
        P = Cm*A
        tails = Am*Tv
        out = []
        for r in range(len(C)):
            tot = arb(0)
            for n in range(N):
                tot += arb(P[r, n].abs_upper())
            tot += tails[r, 0]
            out.append(arb(tot.upper()))
        return out
    finally:
        ctx.prec = old


def certified_sup_family(t0, delta, S, C, Ksub=2):
    """RIGOROUS sup bounds on [t0, t0+delta] for every vector in the family C."""
    t0 = Fraction(t0)
    delta = Fraction(delta)
    lam_max = max(lam_f(p) for p in S)
    cmax = max(1, max(abs(x) for v in C for x in v))
    lc = math.log(cmax)
    top = float(t0 + delta)
    prec = int(160 + 1.6*(lam_max*top + lc)/LOG2 + 6*len(S))
    prec = (prec//64 + 1)*64
    N = auto_N(lam_max*float(delta)/(2*Ksub), lam_max*top + lc + 60)
    h = delta/(2*Ksub)
    best = None
    for k in range(Ksub):
        c0 = t0 + delta*(2*k + 1)/(2*Ksub)
        b = _bound_family(c0, h, S, C, N, prec)
        best = b if best is None else [x if x > y else y for x, y in zip(b, best)]
    return best


def rank_profile(t0, delta, S, logsigma=140, Ksub=2):
    """r = number of LINEARLY INDEPENDENT integer polynomials on the common support S that
    this search certifies subunit on the block.  Strict total positivity of {exp(lam t)}
    then PROVES the block carries at most |S| - r points of Sol (rank-codimension trap).
    Returns (r, list of certified coefficient vectors)."""
    q = len(S)
    R = build_lattice(t0, delta, S, logsigma).lll()
    rows = [[int(R[i, k]) for k in range(q)] for i in range(q)]
    rows = [v for v in rows if any(v)]
    bs = certified_sup_family(t0, delta, S, rows, Ksub=Ksub)
    good = [v for v, b in zip(rows, bs) if b < 1]
    if not good:
        return 0, []
    return fmpz_mat([list(v) for v in good]).rank(), good


def auto_N(y, target):
    N = 6
    while True:
        v = N*math.log(y/2 + 1e-300) - math.lgamma(N + 1)
        if -v > target and N > 2*y + 6:
            return N
        N += 4


def certified_sup(t0, delta, S, c, Ksub=8, prec=None, N=None):
    """RIGOROUS upper bound on sup_{t in [t0, t0+delta]} |sum_e c_e exp(lambda_e t)|."""
    t0 = Fraction(t0)
    delta = Fraction(delta)
    lam_max = max(lam_f(p) for p in S)
    cmax = max(1, max(abs(x) for x in c))
    lc = math.log(cmax)
    top = float(t0 + delta)
    if prec is None:
        prec = int(160 + 1.6*(lam_max*top + lc)/LOG2 + 6*len(S))
        prec = (prec//64 + 1)*64
    if N is None:
        N = auto_N(lam_max*float(delta)/(2*Ksub), lam_max*top + lc + 60)
    h = delta/(2*Ksub)
    best = None
    for k in range(Ksub):
        c0 = t0 + delta*(2*k + 1)/(2*Ksub)
        b = _block_bound(c0, h, S, c, N, prec)
        best = b if best is None or b > best else best
    return best


# --------------------------------------------------------------------------
#  LLL search (heuristic; every output is re-certified above)
# --------------------------------------------------------------------------
def build_lattice(t0, delta, S, logsigma=140):
    q = len(S)
    t0 = Fraction(t0)
    delta = Fraction(delta)
    lam_max = max(lam_f(p) for p in S)
    top = float(t0 + delta)
    N = auto_N(lam_max*float(delta)/2, lam_max*top + 130)
    prec = int(220 + 1.6*lam_max*top/LOG2 + 8*q + 2*N + logsigma)
    prec = (prec//64 + 1)*64
    old = ctx.prec
    ctx.prec = prec
    try:
        W, K, T = cheb_rows(t0 + delta/2, delta/2, S, N, prec)
        sig = arb(2)**logsigma
        M = [[0]*(q + N + q) for _ in range(q)]
        for e in range(q):
            M[e][e] = 1
            for n in range(N):
                M[e][q + n] = to_int(sig*W[e]*K[e][n])
            M[e][q + N + e] = to_int(sig*W[e]*T[e]) + 1
        return fmpz_mat(M)
    finally:
        ctx.prec = old


def candidates(t0, delta, S, logsigma=140, ncomb=3):
    q = len(S)
    R = build_lattice(t0, delta, S, logsigma).lll()
    rows = [[int(R[r, k]) for k in range(q)] for r in range(q)]
    out = [r for r in rows[:6] if any(r)]
    top = rows[:ncomb]
    for co in itertools.product((-2, -1, 0, 1, 2), repeat=len(top)):
        if all(x == 0 for x in co):
            continue
        v = [sum(co[k]*top[k][e] for k in range(len(top))) for e in range(q)]
        if any(v):
            out.append(v)
    seen, uniq = set(), []
    for v in out:
        g = 0
        for x in v:
            g = math.gcd(g, abs(x))
        if g > 1:
            v = [x//g for x in v]
        if tuple(v) in seen:
            continue
        seen.add(tuple(v))
        uniq.append(v)
    return uniq


def search(t0, delta, S, logsigmas=(140, 260), screen=6, Ksub=8):
    """Best (rigorous bound, c) this search found; None if nothing nonzero came out."""
    best = None
    for ls in logsigmas:
        try:
            uniq = candidates(t0, delta, S, ls)
        except Exception:
            continue
        scored = sorted(((float(certified_sup(t0, delta, S, v, Ksub=1).mid()), v)
                         for v in uniq), key=lambda p: p[0])
        for _, v in scored[:screen]:
            b = certified_sup(t0, delta, S, v, Ksub=Ksub)
            if best is None or b < best[0]:
                best = (b, v)
            if best[0] < 1:
                return best
    return best


# --------------------------------------------------------------------------
#  supports
# --------------------------------------------------------------------------
def lam_sorted(q):
    """The q pairs (i,j) in N_0^2 of least frequency i log2 + j log3 (weighted simplex)."""
    pts = sorted((lam_f((i, j)), i, j)
                 for i in range(0, 2*q + 3) for j in range(0, 2*q + 3)
                 if lam_f((i, j)) <= q + 4)
    return [(i, j) for (_, i, j) in pts[:q]]


def deg_simplex(d):
    return [(i, j) for i in range(d + 1) for j in range(d + 1 - i)]


# --------------------------------------------------------------------------
#  covolume capacity index (prediction only, never used for a claim)
# --------------------------------------------------------------------------
def capacity_index(t0, delta, S):
    q = len(S)
    t0 = Fraction(t0)
    delta = Fraction(delta)
    lam_max = max(lam_f(p) for p in S)
    top = float(t0 + delta)
    N = auto_N(lam_max*float(delta)/2, lam_max*top + 130)
    prec = int(220 + 1.6*lam_max*top/LOG2 + 8*q + 2*N)
    prec = (prec//64 + 1)*64
    old = ctx.prec
    ctx.prec = prec
    try:
        W, K, _ = cheb_rows(t0 + delta/2, delta/2, S, N, prec)
        B = [[W[e]*K[e][n] for n in range(N)] for e in range(q)]
        tot = arb(0)
        basis = []
        for e in range(q):
            v = B[e]
            for (u, nu2) in basis:
                cc = sum((v[k]*u[k] for k in range(N)), arb(0))/nu2
                v = [v[k] - cc*u[k] for k in range(N)]
            nu2 = sum((x*x for x in v), arb(0))
            basis.append((v, nu2))
            tot += nu2.log()/2
        lc = float(tot.mid())
    finally:
        ctx.prec = old
    return lc/q + 0.5*(math.log(2/math.pi) + (2.0/q)*math.lgamma(q/2.0 + 1))


# --------------------------------------------------------------------------
#  drivers
# --------------------------------------------------------------------------
def qmin(t0, delta=1, lo=3, cap=400, log=lambda s: None):
    """Smallest |S| (over the nested weighted-simplex family) at which THIS search
    produced a rigorously certified subunit polynomial.  Upper bound for the true min."""
    q = lo
    while True:
        r = search(t0, delta, lam_sorted(q))
        log(f"      q={q}: {float(r[0].mid()) if r else float('inf'):.6g}")
        if r and r[0] < 1:
            break
        q *= 2
        if q > cap:
            return None
    hi, lo2, ok = q, q//2, (q, r)
    while lo2 + 1 < hi:
        mid = (lo2 + hi)//2
        r = search(t0, delta, lam_sorted(mid))
        log(f"      q={mid}: {float(r[0].mid()) if r else float('inf'):.6g}")
        if r and r[0] < 1:
            hi, ok = mid, (mid, r)
        else:
            lo2 = mid
    return ok


def cmd_sweep(Ls, verbose=False, dump=None):
    log = print if verbose else (lambda s: None)
    print(f"{'L':>4} {'q_min':>6} {'deg':>4} {'lam_max':>8} {'cert. sup <=':>13} "
          f"{'log10|c|max':>12} {'defect/L':>9} {'time':>7}")
    out = {}
    for L in Ls:
        t = time.time()
        o = qmin(L, 1, log=log)
        if o is None:
            print(f"{L:4d}   FAIL")
            continue
        q, (b, c) = o
        S = lam_sorted(q)
        out[L] = dict(q=q, S=[list(p) for p in S], c=[int(x) for x in c], bound=str(b))
        print(f"{L:4d} {q:6d} {max(i + j for i, j in S):4d} {max(map(lam_f, S)):8.3f} "
              f"{float(b.mid()):13.6f} {math.log10(max(abs(x) for x in c)):12.2f} "
              f"{(q - 1)/L:9.3f} {time.time() - t:6.1f}s")
        sys.stdout.flush()
    if dump:
        json.dump(out, open(dump, "w"))


def cmd_cover(L, Ks=(1, 2, 4)):
    print(f"block [{L},{L+1}) split into K equal pieces; capacity = sum of the defects")
    print(f"{'K':>3} {'|S| per piece':>16} {'total capacity':>15}")
    for K in Ks:
        pieces = []
        for k in range(K):
            o = qmin(Fraction(L*K + k, K), Fraction(1, K))
            if o is None:
                pieces = None
                break
            pieces.append(o[0])
        if pieces is None:
            print(f"{K:3d} {'FAIL':>16}")
        else:
            print(f"{K:3d} {str(pieces):>16} {sum(p - 1 for p in pieces):15d}")
        sys.stdout.flush()


def cmd_long(L, deltas=(1, 2, 4, 8), beta=14.0):
    """beta = 14 is the kernel-verified lower bound for the least generator."""
    print(f"{'delta':>6} {'q_min':>6} {'defect':>7} {'pressure>=':>11} {'deficiency':>11}")
    for d in deltas:
        o = qmin(L, d)
        if o is None:
            print(f"{d:6} FAIL")
            continue
        q = o[0]
        press = ((L + d)**2 - L**2)/(2*beta)
        print(f"{d:6} {q:6d} {q - 1:7d} {press:11.3f} {(q - 1)/press:11.2f}")
        sys.stdout.flush()


def cmd_shapes(L, q, ntrials=200, seed=1):
    random.seed(seed)
    pool = lam_sorted(3*q)
    dense = lam_sorted(q)
    print(f"L={L}  q={q}   (capacity index: lower is better; PREDICTION only)")
    print(f"  weighted simplex   cap={capacity_index(L,1,dense):+9.4f}  lam_max={max(map(lam_f,dense)):7.3f}")
    td = sorted(pool, key=lambda p: (p[0] + p[1], lam_f(p)))[:q]
    print(f"  total-degree order cap={capacity_index(L,1,td):+9.4f}  lam_max={max(map(lam_f,td)):7.3f}")
    best = None
    for _ in range(ntrials):
        S = random.sample(pool, q)
        cc = capacity_index(L, 1, S)
        if best is None or cc < best[0]:
            best = (cc, S)
    print(f"  best random sparse cap={best[0]:+9.4f}  lam_max={max(map(lam_f,best[1])):7.3f}  (of {ntrials})")
    for name, extra in (("(3,0),(0,2)   dlam=.118", [(3, 0), (0, 2)]),
                        ("(8,0),(0,5)   dlam=.052", [(8, 0), (0, 5)]),
                        ("(19,0),(0,12) dlam=.014", [(19, 0), (0, 12)]),
                        ("(84,0),(0,53) dlam=.002", [(84, 0), (0, 53)])):
        S = [p for p in lam_sorted(q + 6) if p not in extra][:q - 2] + extra
        print(f"  near-resonant {name:24s} cap={capacity_index(L,1,S):+9.4f}  lam_max={max(map(lam_f,S)):7.3f}")
    for trial in range(3):
        cur = random.sample(pool, q)
        curc = capacity_index(L, 1, cur)
        for _ in range(60):
            improved = False
            for out in list(cur):
                for inn in pool:
                    if inn in cur:
                        continue
                    T = [p for p in cur if p != out] + [inn]
                    cc = capacity_index(L, 1, T)
                    if cc < curc - 1e-9:
                        cur, curc, improved = T, cc, True
                        break
                if improved:
                    break
            if not improved:
                break
        print(f"  swap-local-search from random start {trial}: cap={curc:+9.4f}  "
              f"equals weighted simplex? {sorted(cur) == sorted(dense)}")
    for name, S in (("weighted simplex", dense), ("best random sparse", best[1])):
        r = search(L, 1, S)
        v = float(r[0].mid()) if r else float("inf")
        print(f"  LLL certified sup, {name:19s}: {v:.6g}   {'CERTIFIED' if v < 1 else 'no certificate'}")


def cmd_verify(path=None):
    path = path or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "near_curve_certificates.json")
    data = json.load(open(path))
    print(f"{'L':>4} {'|S|':>4} {'rigorous sup bound':>26} {'verdict':>8}")
    allok = True
    for L in sorted(data, key=int):
        d = data[L]
        S = [tuple(p) for p in d["S"]]
        c = [int(x) for x in d["c"]]
        b = certified_sup(int(L), 1, S, c, Ksub=8)
        ok = bool(b < 1)
        allok &= ok
        print(f"{int(L):4d} {len(S):4d} {str(b):>26} {'PROVED' if ok else 'FAIL':>8}")
    print("all certificates re-verified with rigorous arb enclosures"
          if allok else "SOME CERTIFICATES FAILED")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    a = sys.argv[2:]
    if cmd == "sweep":
        cmd_sweep([int(x) for x in a] or list(range(1, 15)), verbose=True)
    elif cmd == "verify":
        cmd_verify(a[0] if a else None)
    elif cmd == "shapes":
        cmd_shapes(int(a[0]), int(a[1]), int(a[2]) if len(a) > 2 else 200)
    elif cmd == "cover":
        cmd_cover(int(a[0]))
    elif cmd == "long":
        cmd_long(int(a[0]))
    else:
        print(__doc__)
