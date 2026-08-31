"""Stage 2b: remaining experiments (log-Cesaro, annular maxima, valleys, variance, Lambert)."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize_scalar
from scipy.special import lambertw

LOG2 = np.log(2.0); LOGPI = np.log(np.pi); a = LOG2
rho1 = 0.661322602060565
kappa1 = (LOGPI + a/2 - np.log(rho1)) / a
A1 = 0.0912661241
gx, gw = leggauss(24)

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

def log_g(x, kap):
    L = np.log(x)
    return -L*L/(2*a) - kap*L

print("=== J. Log-Cesaro: (1/log(t/t0)) int_{t0}^t |f|/(A1' g) dx/x for mantissas y ===")
t0 = 8.0
# precompute per-unit-interval integrals of |f|/g * 1/x up to 3*2^13
maxm = int(1.75 * 2**13) + 2
ms_all = np.arange(8, maxm)
log_ints = {}
B = 8192
vals_all = np.zeros(len(ms_all))
for i in range(0, len(ms_all), B):
    mb = ms_all[i:i+B].astype(float)
    xx = mb[:, None] + 0.5 + 0.5*gx[None, :]
    xf = xx.ravel()
    v = (np.exp(log_abs_f(xf) - log_g(xf, kappa1)) / xf).reshape(len(mb), -1)
    vals_all[i:i+B] = (v @ gw) * 0.5
cum = np.concatenate([[0.0], np.cumsum(vals_all)])  # cum[j] = int over [8, 8+j)
mants = [1.0, 1.25, 1.5, 1.75]
print("  entries: (1/log(t/8)) * int |f|/g dx/x   for y=1, 1.25, 1.5, 1.75")
res_logces = {}
for n in range(5, 14):
    row = []
    for ymant in mants:
        t = ymant * 2**n
        m0 = int(np.floor(t))
        s = cum[m0 - 8]
        if t > m0:
            mid = (m0 + t)/2; half = (t - m0)/2
            xf = mid + half*gx
            s += float(np.dot(np.exp(log_abs_f(xf) - log_g(xf, kappa1))/xf, gw) * half)
        row.append(s / np.log(t/t0))
    res_logces[n] = row
    print(f"n={n:2d}: " + "  ".join(f"{r:.6f}" for r in row))
print("(should converge to a single constant A1' for ALL mantissas if log-averaging kills the phase)")

print()
print("=== K+N. Annular maxima M_k and Lambert-approximation residual (sol 2) ===")
sol2 = {3:(-11.251778,1.177288),4:(-15.485667,1.162272),5:(-20.390823,1.168960),
        6:(-25.991031,1.165501),7:(-32.287929,1.167235),8:(-39.274011,1.166376),
        9:(-46.956338,1.166810),10:(-55.329708,1.166594),11:(-64.397553,1.166703),
        12:(-74.157742,1.166649)}
beta = np.log(np.sqrt(3)/2); lam = LOG2
c = lam/np.pi*np.sqrt(1.5)
print(" k   log M_k (mine)   x*/2^k     sol2 log M_k   sol2 x*/2^k   Lambert A_k   resid")
for k in range(3, 13):
    lo, hi = 2**k, 2**(k+1)
    best = (-np.inf, None, None)
    ms = np.arange(lo, hi)
    # coarse scan vectorized
    offs = np.linspace(0.02, 0.98, 25)
    Bm = 2048
    for i in range(0, len(ms), Bm):
        mb = ms[i:i+Bm]
        xx = (mb[:, None] + offs[None, :]).astype(float)
        lv = log_abs_f(xx.ravel()).reshape(len(mb), -1)
        j = np.unravel_index(np.argmax(lv), lv.shape)
        if lv[j] > best[0]:
            best = (lv[j], int(mb[j[0]]), offs[j[1]])
    m = best[1]
    r = minimize_scalar(lambda t: -log_abs_f(np.array([m + t]))[0], bounds=(0.001, 0.999),
                        method='bounded', options={'xatol':1e-12})
    logM = -r.fun; xstar = (m + r.x)/2**k
    n = k + 1
    w = float(lambertw(c*n).real)
    Ak = -lam/2*k*(k+1) - n*LOGPI + n*beta - (w*w + 2*w)/(2*lam)
    s2 = sol2.get(k, (np.nan, np.nan))
    print(f"{k:2d}  {logM:12.6f}  {xstar:.6f}   {s2[0]:12.6f}   {s2[1]:.6f}   {Ak:12.6f}  {logM-Ak:+.6f}")

print()
print("=== L. Dyadic valleys E_{2^k} = max on (2^k, 2^k+1) vs (H1^2/(e(k+1))) 2^{-k(k+1)} ===")
H1 = float(np.exp(log_abs_f(np.array([0.5]))[0]))
print(f"H(1) = {H1:.15f}")
print(" k   log E_2^k      prediction     diff      peak t*   1-1/(k+1)")
for k in range(4, 13):
    m = 2**k
    r = minimize_scalar(lambda t: -log_abs_f(np.array([m + t]))[0], bounds=(0.5, 0.999999),
                        method='bounded', options={'xatol':1e-13})
    logE = -r.fun; tpk = r.x
    pred = 2*np.log(H1) - 1 - np.log(k+1) - k*(k+1)*LOG2
    print(f"{k:2d}  {logE:12.5f}  {pred:12.5f}  {logE-pred:+.5f}   {tpk:.6f}  {1-1/(k+1):.6f}")

print()
print("=== M. Variance of S_N (exact odd-mantissa orbits): sigma^2 = pi^2/4 vs pi^2/2 ===")
rng = np.random.default_rng(7)
N = 34; M = 400000
m0 = rng.integers(0, 2**51, size=M).astype(np.float64)
t = (2.0*m0 + 1.0) / 2.0**52
S = np.zeros(M)
for j in range(N):
    S += np.log(np.abs(2*np.sin(np.pi*t)))
    t = (2*t) % 1.0
ok = np.isfinite(S)
mean_S = S[ok].mean(); var_S = S[ok].var()
pred4 = N*np.pi**2/4 - np.pi**2/3
pred2 = N*np.pi**2/2 - 2*np.pi**2/3
print(f"finite: {ok.sum()}/{M};  mean S_N = {mean_S:.4f} (predict 0)")
print(f"Var(S_{N}) = {var_S:.3f}")
print(f"  prediction with sigma^2=pi^2/4 (Green-Kubo): {pred4:.3f}")
print(f"  prediction with sigma^2=pi^2/2            : {pred2:.3f}")
# also N=20 as cross-check of the constant -pi^2/3 correction
N2 = 20
t = (2.0*m0 + 1.0) / 2.0**52
S2 = np.zeros(M)
for j in range(N2):
    S2 += np.log(np.abs(2*np.sin(np.pi*t)))
    t = (2*t) % 1.0
ok2 = np.isfinite(S2)
print(f"N={N2}: Var = {S2[ok2].var():.3f}; pred(pi^2/4) = {N2*np.pi**2/4 - np.pi**2/3:.3f}; pred(pi^2/2) = {N2*np.pi**2/2 - 2*np.pi**2/3:.3f}")

print()
print("=== O. Mantissa profile P(y) from transfer operator vs direct Cesaro (sec I) ===")
# F(z) = lim rho^{-n} int_0^z f1 P_n dx / A1-part; direct at n=13,14 via fine quadrature.
gx16, gw16 = leggauss(16)
def log_P(n, tt):
    out = np.zeros_like(tt)
    for j in range(n):
        out += np.log(np.abs(np.sin(np.pi * (2.0 ** j) * tt)))
    return out
def W_kappa_vec(y, kap):
    return np.exp(log_abs_f(y)) * y**kap * np.exp(np.log(y)**2/(2*a))
def partial_F(n, z):
    """rho^{-n} int_0^z f1(x) P_n(x) dx, f1(x) = W_{k1}((x+1)/2)"""
    panels = int(np.ceil(z * 2**n))
    edges = np.minimum(np.arange(panels+1) / 2**n, z)
    tot = 0.0
    B = 8192
    for i in range(0, panels, B):
        aa = edges[i:min(i+B,panels)]; bb = edges[i+1:min(i+B,panels)+1]
        mid = (aa+bb)/2; half = (bb-aa)/2
        xx = (mid[:, None] + half[:, None]*gx16[None, :]).ravel()
        v = (np.exp(log_P(n, xx)) * W_kappa_vec((xx+1)/2, kappa1)).reshape(-1, 16)
        tot += float(np.sum((v @ gw16) * half))
    return tot / rho1**n
n = 13
denom = partial_F(n, 1.0)
print(f"n={n}: rho^-n int_0^1 f1 P_n = {denom:.8f} (matches 2*A1? A1={A1}; note shell mean = int = A1... check: {denom:.8f} vs {A1:.8f})")
zs = [0.25, 0.5, 0.75, 0.9]
for z in zs:
    Fz = partial_F(n, z) / denom
    y = (1+z)/2*2  # x=2y-1 => y=(x+1)/2, mantissa in [1,2]: y_m = 1+z... careful: shells [2^{n-1},2^n], y in [1/2,1], x=2y-1
    # profile at T = 2^n * y with y=(z+1)/2 in sol4 param: P(y) = (1+F(z))/(2y)
    ym = (z+1)/2
    P = (1 + Fz) / (2*ym)
    print(f"z={z:.2f} (t=2^n*{2*ym:.3f}... i.e. mantissa {2*ym:.3f}): F(z)={Fz:.6f}, P={P:.6f}")
print("compare direct Cesaro limits (sec I): y=1.25 -> 0.9716, y=1.5 -> 1.0864, y=1.75 -> 1.1000")
