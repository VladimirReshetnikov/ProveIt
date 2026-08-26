"""Stage 2: shell means of |f|/g, Cesaro profiles, annular maxima, dyadic valleys,
variance re-test, Lambert-approximation table, log-Cesaro test.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss

LOG2 = np.log(2.0); LOGPI = np.log(np.pi); a = LOG2

def log_abs_f(x):
    x = np.asarray(x, dtype=float)
    H = int(np.ceil(np.log2(np.pi * float(np.max(x))))) + 30
    out = np.zeros_like(x)
    for h in range(H + 1):
        u = np.pi * x / (2.0 ** h)
        small = u < 1e-4
        t = np.where(small, 1.0, u)
        with np.errstate(divide='ignore', invalid='ignore'):
            big_term = np.log(np.abs(np.sin(t))) - np.log(t)
        out += np.where(small, -u*u/6.0 - u**4/180.0, big_term)
    return out

# ---- constants from stage 1
rho1 = 0.661322602060565
kappa1 = (LOGPI + a/2 - np.log(rho1)) / a
kappa0 = 1.5 + LOGPI / a
kappainf = (LOGPI + a/2 - np.log(np.sqrt(3)/2)) / a

def log_g(x, kap):
    L = np.log(x)
    return -L*L/(2*a) - kap*L

print("=== G. Shell means J_n = (1/2^{n-1}) int_{2^{n-1}}^{2^n} |f|/g_{kappa1} dx ===")
gx, gw = leggauss(24)
def shell_mean(n, kap, log_extra=None, upto=None):
    """mean over [2^{n-1}, min(2^n, upto)] of |f|/g; per-unit-interval 24pt Gauss.
       Returns (integral, length). log_extra(x): add to -log g (e.g. -log x for log-Cesaro)."""
    lo = 2 ** (n - 1); hi = 2 ** n if upto is None else min(2 ** n, upto)
    ms = np.arange(lo, int(np.ceil(hi)))
    total = 0.0
    B = 4096  # batch unit intervals
    for i in range(0, len(ms), B):
        mb = ms[i:i+B].astype(float)
        left = np.maximum(mb, lo); right = np.minimum(mb + 1, hi)
        mid = (left + right)/2; half = (right - left)/2
        xx = mid[:, None] + half[:, None]*gx[None, :]
        xf = xx.ravel()
        lv = log_abs_f(xf) - log_g(xf, kap)
        if log_extra is not None:
            lv = lv + log_extra(xf)
        v = np.exp(lv).reshape(len(mb), -1)
        total += float(np.sum((v @ gw) * half))
    return total, hi - lo

print(" n   shell mean of |f|/g_k1     (predict -> const A1)")
A1_direct = []
for n in range(4, 15):
    tot, ln = shell_mean(n, kappa1)
    A1_direct.append(tot/ln)
    print(f"{n:2d}   {tot/ln:.10f}")

print()
print("=== H. Transfer-operator prediction of the same shell means ===")
def collocation_matrix(N, q=1):
    j = np.arange(N + 1)
    x = (1 - np.cos(np.pi * j / N)) / 2
    w = np.ones(N + 1); w[0] = 0.5; w[N] = 0.5; w *= (-1.0) ** j
    def interp_matrix(pts):
        D = pts[:, None] - x[None, :]
        exact = np.abs(D) < 1e-14
        D = np.where(exact, 1.0, D)
        C = w[None, :] / D
        M = C / np.sum(C, axis=1)[:, None]
        M[np.any(exact, axis=1)] = 0.0
        idx = np.where(exact)
        M[idx[0], idx[1]] = 1.0
        return M
    A = interp_matrix(x / 2); B = interp_matrix((x + 1) / 2)
    L = 0.5 * (np.sin(np.pi*x/2)[:, None]**q * A + np.cos(np.pi*x/2)[:, None]**q * B)
    return L, x

def clenshaw_curtis_weights(N):
    # weights for nodes x_j=(1-cos(j pi/N))/2 on [0,1]
    j = np.arange(N+1)
    wcc = np.zeros(N+1)
    v = np.zeros(N+1)
    for jj in range(N+1):
        s = 0.0
        for k in range(0, N//2 + 1):
            ck = 1.0 if (k==0 or 2*k==N) else 2.0
            s += ck/(1-4*k**2) * np.cos(2*k*jj*np.pi/N)
        v[jj] = s
    wcc = 2.0/N * v
    wcc[0] *= 0.5; wcc[N] *= 0.5
    return wcc/2.0  # interval length 1 (nodes on [0,1]: standard CC on [-1,1] scaled)

N = 40
L1m, xn = collocation_matrix(N, 1)
wcc = clenshaw_curtis_weights(N)
# sanity CC: integrate x^2 -> 1/3
print(f"CC weight sanity: int x^2 = {np.dot(wcc, xn**2):.12f} (should be 0.333...)")

def W_kappa_vec(y, kap):
    return np.exp(log_abs_f(y)) * y**kap * np.exp(np.log(y)**2/(2*a))
f1 = W_kappa_vec((xn + 1)/2, kappa1)
vec = f1.copy()
pred = []
for n in range(1, 61):
    vec = (L1m @ vec) / rho1
    if 4 <= n <= 14 or n in (20, 30, 40, 60):
        pred.append((n, np.dot(wcc, vec)))
print(" n   rho^{-n} int L^n f1   (same object as direct shell mean; -> A1)")
for n, p in pred:
    print(f"{n:2d}   {p:.10f}")
A1 = pred[-1][1]
print(f"A1 (transfer-operator limit) = {A1:.10f}")

print()
print("=== I. Cesaro running mean with g = A1 * g_kappa1: dyadic vs non-dyadic t ===")
# R(t) = (1/(t-t0)) int_{t0}^t |f|/(A1 g) dx, t0 = 8
t0 = 8.0
# accumulate per unit interval up to 2^14
tops = []
cum = 0.0
unit_int = {}
for n in range(4, 15):
    lo = 2**(n-1)
    ms = np.arange(lo, 2**n)
    B = 4096
    for i in range(0, len(ms), B):
        mb = ms[i:i+B].astype(float)
        mid = mb + 0.5; half = 0.5
        xx = mid[:, None] + half*gx[None, :]
        xf = xx.ravel()
        v = np.exp(log_abs_f(xf) - log_g(xf, kappa1)).reshape(len(mb), -1)
        vals = (v @ gw) * half
        for m_, val in zip(mb.astype(int), vals):
            unit_int[m_] = val
mants = [1.0, 1.25, 1.5, 1.75]
print("  t = y*2^n; entries R(t) for y=1, 1.25, 1.5, 1.75")
for n in range(5, 15):
    row = []
    for ymant in mants:
        t = ymant * 2**n
        # integral from t0 to t: full unit intervals [8, floor(t)) + partial
        full = sum(unit_int[m] for m in range(8, int(np.floor(t))))
        # partial piece
        m0 = int(np.floor(t))
        if t > m0:
            mid = (m0 + t)/2; half = (t - m0)/2
            xf = mid + half*gx
            pv = float(np.dot(np.exp(log_abs_f(xf) - log_g(xf, kappa1)), gw) * half)
        else:
            pv = 0.0
        R = (full + pv) / (A1 * (t - t0))
        row.append(R)
    print(f"n={n:2d}: " + "  ".join(f"{r:.6f}" for r in row))

print()
print("=== J. Log-Cesaro (multiplicative average): (1/log(t/t0)) int |f|/g dx/x ===")
for n in range(5, 15):
    row = []
    for ymant in mants:
        t = ymant * 2**n
        full = 0.0
        # recompute with 1/x weight per unit interval (cheap: reuse Gauss but need /x) - do direct
        ms = np.arange(8, int(np.floor(t)))
        B = 8192
        s = 0.0
        for i in range(0, len(ms), B):
            mb = ms[i:i+B].astype(float)
            xx = mb[:, None] + 0.5 + 0.5*gx[None, :]
            xf = xx.ravel()
            v = (np.exp(log_abs_f(xf) - log_g(xf, kappa1)) / xf).reshape(len(mb), -1)
            s += float(np.sum((v @ gw) * 0.5))
        m0 = int(np.floor(t))
        if t > m0:
            mid = (m0 + t)/2; half = (t - m0)/2
            xf = mid + half*gx
            s += float(np.dot(np.exp(log_abs_f(xf) - log_g(xf, kappa1))/xf, gw) * half)
        R = s / np.log(t/t0)
        row.append(R)
    print(f"n={n:2d}: " + "  ".join(f"{r:.6f}" for r in row))

print()
print("=== K. Annular maxima M_k = max on [2^k, 2^{k+1}]  (vs sol 2 table) ===")
sol2 = {3:(-11.251778,1.177288),4:(-15.485667,1.162272),5:(-20.390823,1.168960),
        6:(-25.991031,1.165501),7:(-32.287929,1.167235),8:(-39.274011,1.166376),
        9:(-46.956338,1.166810),10:(-55.329708,1.166594),11:(-64.397553,1.166703),
        12:(-74.157742,1.166649)}
from scipy.optimize import minimize_scalar
for k in range(3, 13):
    lo, hi = 2**k, 2**(k+1)
    best = (-np.inf, None)
    for m in range(lo, hi):
        xs = m + np.linspace(0.02, 0.98, 25)
        lv = log_abs_f(xs)
        j = int(np.argmax(lv))
        if lv[j] > best[0]:
            best = (lv[j], m, xs[j])
    # refine around best
    m = best[1]
    r = minimize_scalar(lambda t: -log_abs_f(np.array([m + t]))[0], bounds=(0.001, 0.999), method='bounded',
                        options={'xatol':1e-12})
    logM = -r.fun; xstar = m + r.x
    s2 = sol2.get(k)
    print(f"k={k:2d}: log M_k = {logM:.6f} at x/2^k = {xstar/2**k:.6f}"
          + (f"   [sol2: {s2[0]:.6f} at {s2[1]:.6f}]" if s2 else ""))

print()
print("=== L. Dyadic valleys E_{2^k} = max on (2^k, 2^k+1) vs H(1)^2/(e(k+1)) 2^{-k(k+1)} ===")
H1 = float(np.exp(log_abs_f(np.array([0.5]))[0]))
for k in range(4, 13):
    m = 2**k
    r = minimize_scalar(lambda t: -log_abs_f(np.array([m + t]))[0], bounds=(0.5, 0.99999), method='bounded',
                        options={'xatol':1e-13})
    logE = -r.fun; tpk = r.x
    pred = 2*np.log(H1) - 1 - np.log(k+1) - k*(k+1)*LOG2
    print(f"k={k:2d}: log E = {logE:.5f}, predict {pred:.5f}, diff = {logE-pred:+.5f}; peak at t = {tpk:.6f} (predict 1-1/(k+1)={1-1/(k+1):.6f})")

print()
print("=== M. Variance re-test with odd-mantissa initial points (exact orbits) ===")
rng = np.random.default_rng(7)
N = 34; M = 200000
m0 = rng.integers(0, 2**51, size=M)
t = (2.0*m0 + 1.0) / 2.0**52   # odd/2^52: orbit exact, never hits 0 for j<52
S = np.zeros(M)
for j in range(N):
    S += np.log(np.abs(2*np.sin(np.pi*t)))
    t = (2*t) % 1.0
ok = np.isfinite(S)
print(f"finite samples: {ok.sum()}/{M}")
mean_S = S[ok].mean(); var_S = S[ok].var()
pred = N*np.pi**2/4 - np.pi**2/3
print(f"N={N}: mean S_N = {mean_S:.4f} (predict 0);  Var = {var_S:.3f}  vs prediction {pred:.3f} (pi^2/4 rate)")
print(f"      vs pi^2/2-rate prediction {N*np.pi**2/2 - 2*np.pi**2/3:.3f}")
print(f"per-step: {(var_S + np.pi**2/3)/N:.4f}; pi^2/4 = {np.pi**2/4:.4f}")

print()
print("=== N. Lambert-approximation residual (sol 2 eq A_k) ===")
from scipy.special import lambertw
beta = np.log(np.sqrt(3)/2); lam = LOG2
c = lam/np.pi*np.sqrt(1.5)
for k in range(3, 13):
    n = k + 1
    w = float(lambertw(c*n).real)
    Ak = -lam/2*k*(k+1) - n*LOGPI + n*beta - (w*w + 2*w)/(2*lam)
    # recompute logM quickly from section K results? redo brief:
    lo = 2**k
    best = -np.inf; bm = None
    for m in range(lo, 2**(k+1)):
        xs = m + np.linspace(0.02, 0.98, 25)
        lv = log_abs_f(xs).max()
        if lv > best: best, bm = lv, m
    r = minimize_scalar(lambda t: -log_abs_f(np.array([bm + t]))[0], bounds=(0.001, 0.999), method='bounded',
                        options={'xatol':1e-12})
    logM = -r.fun
    print(f"k={k:2d}: log M_k = {logM:.6f}, A_k = {Ak:.6f}, residual = {logM - Ak:+.6f}")
