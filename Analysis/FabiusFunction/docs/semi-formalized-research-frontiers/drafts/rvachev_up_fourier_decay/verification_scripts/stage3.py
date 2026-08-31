"""Stage 3: LIL-scale tail test, covariance check, extended valleys/maxima, H(3) two-adic check,
Sturm certificate, profile grid."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize_scalar
from scipy.special import lambertw
from scipy.stats import norm

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
            big = np.log(np.abs(np.sin(t))) - np.log(t)
        out += np.where(small, -u*u/6.0 - u**4/180.0, big)
    return out

print("=== P. Tail of S_L at the LIL scale: Gaussian with sigma = pi/2? ===")
rng = np.random.default_rng(11)
L = 40; M = 10_000_000
sig = np.pi/2
exceed_levels = np.array([1.5, 2.0, 2.2214, 2.5, 2.9, 3.1416, 3.5])  # units of sqrt(L loglog L)
llog = np.log(np.log(L))
thr = exceed_levels * np.sqrt(L * llog)
cnt = np.zeros(len(thr), dtype=np.int64)
batch = 2_000_000
tot = 0
for b in range(M // batch):
    m0 = rng.integers(0, 2**51, size=batch).astype(np.float64)
    t = (2.0*m0 + 1.0) / 2.0**52
    S = np.zeros(batch)
    for j in range(L):
        S += np.log(np.abs(2*np.sin(np.pi*t)))
        t = (2*t) % 1.0
    ok = np.isfinite(S)
    S = S[ok]; tot += len(S)
    for i, th in enumerate(thr):
        cnt[i] += int(np.sum(S > th))
print(f"L={L}, samples={tot}, sqrt(L llog L)={np.sqrt(L*llog):.3f}")
print(" c      threshold   empirical P(S_L>c sqrt(L llog L))   Gaussian(sigma=pi/2)   Gaussian(sigma=pi/sqrt2)")
for i, cft in enumerate(exceed_levels):
    th = thr[i]
    emp = cnt[i]/tot
    g1 = norm.sf(th/(sig*np.sqrt(L)))
    g2 = norm.sf(th/(np.pi/np.sqrt(2)*np.sqrt(L)))
    print(f"{cft:6.4f}  {th:8.3f}   {emp:.3e}                        {g1:.3e}              {g2:.3e}")

print()
print("=== Q. Covariance c_1 = int psi psi(2x) dx = pi^2/24? ===")
gx, gw = leggauss(64)
def psi(x): return np.log(np.abs(2*np.sin(np.pi*x)))
# integrate over [0,1] avoiding singularities: split at 0, 1/2, 1
tot = 0.0
for (lo, hi) in [(0,0.5),(0.5,1.0)]:
    # further split for singularity at ends: use tanh-sinh-ish: just many panels
    edges = np.linspace(lo, hi, 2001)
    mid = (edges[:-1]+edges[1:])/2; half = (edges[1]-edges[0])/2
    xx = (mid[:, None] + half*gx[None, :]).ravel()
    tot += float(np.sum((psi(xx)*psi((2*xx) % 1.0)).reshape(-1,64) @ gw) * half)
print(f"c_1 = {tot:.8f}; pi^2/24 = {np.pi**2/24:.8f}")

print()
print("=== R. Valleys extended k=13..16 ===")
H1 = float(np.exp(log_abs_f(np.array([0.5]))[0]))
for k in range(13, 17):
    m = 2**k
    r = minimize_scalar(lambda t: -log_abs_f(np.array([m + t]))[0], bounds=(0.7, 0.9999999),
                        method='bounded', options={'xatol':1e-13})
    logE = -r.fun; tpk = r.x
    pred = 2*np.log(H1) - 1 - np.log(k+1) - k*(k+1)*LOG2
    print(f"k={k:2d}: log E = {logE:.5f}, predict {pred:.5f}, diff = {logE-pred:+.5f}, peak t*={tpk:.6f} vs {1-1/(k+1):.6f}")

print()
print("=== S. Two-adic peaks after m*2^k for odd m=3 (sol 2 Thm 7.3) ===")
def log_H_of(z):
    out = 0.0
    for r in range(1, 80):
        u = np.pi * z / 2.0**r
        if u < 1e-4:
            out += -u*u/6.0 - u**4/180.0
        else:
            out += float(np.log(np.abs(np.sin(u)/u)))
    return out
logH3 = log_H_of(3.0)
print(f"|H(3)| = {np.exp(logH3):.10f}")
for k in [6, 8, 10, 12]:
    N = 3*2**k
    r = minimize_scalar(lambda t: -log_abs_f(np.array([N + t]))[0], bounds=(0.5, 0.9999999),
                        method='bounded', options={'xatol':1e-13})
    logE = -r.fun
    pred = np.log(H1) + logH3 - 1 - np.log(k+1) - (k+1)*np.log(N)
    print(f"k={k:2d} (N={N}): log E = {logE:.5f}, sol2 predict {pred:.5f}, diff = {logE-pred:+.5f}")

print()
print("=== T. Annular maxima extended k=13..15 + Lambert residual ===")
beta = np.log(np.sqrt(3)/2); lam = LOG2
c = lam/np.pi*np.sqrt(1.5)
offs = np.linspace(0.02, 0.98, 25)
for k in range(13, 16):
    lo, hi = 2**k, 2**(k+1)
    ms = np.arange(lo, hi)
    best = (-np.inf, None)
    Bm = 4096
    for i in range(0, len(ms), Bm):
        mb = ms[i:i+Bm]
        xx = (mb[:, None] + offs[None, :]).astype(float)
        lv = log_abs_f(xx.ravel()).reshape(len(mb), -1)
        j = np.unravel_index(np.argmax(lv), lv.shape)
        if lv[j] > best[0]:
            best = (lv[j], int(mb[j[0]]))
    m = best[1]
    r = minimize_scalar(lambda t: -log_abs_f(np.array([m + t]))[0], bounds=(0.001, 0.999),
                        method='bounded', options={'xatol':1e-12})
    logM = -r.fun; xstar = (m + r.x)/2**k
    n = k+1
    w = float(lambertw(c*n).real)
    Ak = -lam/2*k*(k+1) - n*LOGPI + n*beta - (w*w+2*w)/(2*lam)
    print(f"k={k:2d}: log M_k = {logM:.6f} at x/2^k={xstar:.6f}; Lambert A_k = {Ak:.6f}; resid {logM-Ak:+.6f}")

print()
print("=== U. Sturm certificate of sol 4 (rho_1 enclosure) -- run verbatim ===")
import sympy as sp
t_ = sp.symbols("t", real=True)
u_ = 2*t_/(1+t_**2)
v_ = (1-t_**2)/(1+t_**2)
c_ = sp.Rational(376189, 10**6)
d_ = sp.Rational(-69093, 10**6)
e_ = sp.Rational(15483, 10**6)
F_ = lambda z: 1 + c_*z + d_*z**2 + e_*z**3
R_ = sp.cancel((u_*F_(u_) + v_*F_(v_)) / (2*F_(2*u_*v_)))
lo_ = sp.Rational(66126807, 10**8)
hi_ = sp.Rational(66134891, 10**8)
okall = True
for expr in (R_ - lo_, hi_ - R_):
    num, den = map(lambda p: sp.Poly(p, t_), sp.together(expr).as_numer_denom())
    c1 = num.eval(0) > 0 and den.eval(0) > 0
    c2 = num.count_roots(0, 1) == 0
    c3 = den.count_roots(0, 1) == 0
    okall = okall and c1 and c2 and c3
    print(f"  expr: eval(0)>0: {c1}, num roots in [0,1]: {num.count_roots(0,1)}, den roots: {den.count_roots(0,1)}")
print(f"CERTIFIED 0.66126807 < rho_1 < 0.66134891: {okall}")

print()
print("=== V. Mantissa profile P(y) on a grid (transfer route, n=13) ===")
rho1 = 0.661322602060565
kappa1 = (LOGPI + a/2 - np.log(rho1)) / a
gx16, gw16 = leggauss(16)
def log_P(n, tt):
    out = np.zeros_like(tt)
    for j in range(n):
        out += np.log(np.abs(np.sin(np.pi * (2.0 ** j) * tt)))
    return out
def W_kappa_vec(y, kap):
    return np.exp(log_abs_f(y)) * y**kap * np.exp(np.log(y)**2/(2*a))
n = 13
panels = 2**n
edges = np.arange(panels+1) / panels
mid = (edges[:-1]+edges[1:])/2; half = 0.5/panels
contrib = np.zeros(panels)
B = 8192
for i in range(0, panels, B):
    mm = mid[i:i+B]
    xx = (mm[:, None] + half*gx16[None, :]).ravel()
    v = (np.exp(log_P(n, xx)) * W_kappa_vec((xx+1)/2, kappa1)).reshape(-1, 16)
    contrib[i:i+B] = (v @ gw16) * half
cum = np.concatenate([[0.0], np.cumsum(contrib)]) / rho1**n
denom = cum[-1]
print("mantissa y in [1,2] (t=2^n y);  profile P(y) = (1+F(y-1))/y  [sol3 param]")
ys = np.arange(1.0, 2.0001, 0.1)
prof = []
for ym in ys:
    z = ym - 1
    idx = int(round(z * panels))
    Fz = cum[idx]/denom
    P = (1 + Fz)/ym
    prof.append(P)
    print(f"y={ym:.2f}: F={Fz:.6f}  P(y)={P:.6f}")
print(f"min/max of profile on grid: {min(prof):.6f} / {max(prof):.6f}")
