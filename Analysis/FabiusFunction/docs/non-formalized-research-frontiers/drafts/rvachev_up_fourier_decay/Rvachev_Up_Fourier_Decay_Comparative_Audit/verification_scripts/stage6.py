"""Stage 6: numerics for the two expanded interpretations.

A. Lobe-maxima statistics per shell (all E_n, comparisons with integrals, CLT check).
B. RMS layer: L2 spectrum, A2 constant, L2 mantissa profile, Plancherel/Poisson check,
   discrete Parseval identity, kappa_q vs lognormal table.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss

LOG2 = np.log(2.0); LOGPI = np.log(np.pi); a = LOG2
rho1 = 0.661322602060565
kappa1 = (LOGPI + a/2 - np.log(rho1)) / a
kappa0 = 1.5 + LOGPI / a
kappa2 = np.log(2*np.pi) / a
kappainf = (LOGPI + a/2 - np.log(np.sqrt(3)/2)) / a

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

gx24, gw24 = leggauss(24)

print("=== A1. All lobe maxima and integrals per shell ===")
# cosine-clustered offsets in (0,1), denser near both endpoints
uu = np.linspace(0.004, 0.996, 96)
offs = (1 - np.cos(np.pi * uu)) / 2

def shell_peaks_and_integrals(k):
    lo, hi = 2**k, 2**(k+1)
    ms = np.arange(lo, hi)
    E = np.zeros(len(ms)); I = np.zeros(len(ms))
    B = 2048
    for i in range(0, len(ms), B):
        mb = ms[i:i+B].astype(float)
        xx = (mb[:, None] + offs[None, :]).ravel()
        lv = log_abs_f(xx).reshape(len(mb), -1)
        j = np.argmax(lv, axis=1)
        # parabolic refinement in t on the log values
        j = np.clip(j, 1, len(offs)-2)
        t0 = offs[j-1]; t1 = offs[j]; t2 = offs[j+1]
        f0 = lv[np.arange(len(mb)), j-1]; f1 = lv[np.arange(len(mb)), j]; f2 = lv[np.arange(len(mb)), j+1]
        # fit quadratic through three points (unequal spacing)
        d1 = t1 - t0; d2 = t2 - t1
        denom = d1*d2*(d1+d2)
        A_ = (f0*d2 - f1*(d1+d2) + f2*d1) * 2 / denom
        B_ = (f2 - f0 - A_/2*((t2)**2-(t0)**2)) / (t2 - t0)
        tstar = np.where(A_ < 0, -B_/A_, t1)
        tstar = np.clip(tstar, t0, t2)
        lE = log_abs_f((mb + tstar))
        E[i:i+B] = np.maximum(lE, f1)  # log E_n
        # integral by 24pt Gauss
        xg = (mb[:, None] + 0.5 + 0.5*gx24[None, :]).ravel()
        v = np.exp(log_abs_f(xg)).reshape(len(mb), -1)
        I[i:i+B] = (v @ gw24) * 0.5
    return ms, E, I

for k in [9, 11, 13]:
    ms, logE, I = shell_peaks_and_integrals(k)
    E = np.exp(logE)
    n_mid = ms + 0.5
    # kappa0-centered standardization
    pred0 = -np.log(n_mid)**2/(2*a) - kappa0*np.log(n_mid)
    U = (logE - pred0) / np.sqrt((np.pi**2/4) * k)
    q = np.quantile(U, [0.05, 0.25, 0.5, 0.75, 0.95])
    from scipy.stats import norm
    qn = norm.ppf([0.05, 0.25, 0.5, 0.75, 0.95])
    fr = np.mean(np.abs(logE - pred0) <= 0.1 * k * a)  # within e^{±0.1 k ln2}
    ratio_sum = E.sum() / I.sum()
    rEI = E / I
    print(f"k={k:2d}: quantiles of standardized (logE - kappa0 line)/sigma sqrt(k):")
    print(f"        {np.round(q,3)}  vs normal {np.round(qn,3)}")
    print(f"        fraction with |dev| <= 0.1*k*ln2: {fr:.3f}")
    print(f"        sum(E_n)/int_shell |f| = {ratio_sum:.4f};  E/I per lobe: median {np.median(rEI):.3f}, max {rEI.max():.3f} (at n=2^k+{ms[np.argmax(rEI)]-2**k})")
    print(f"        min log E at n=2^k+{ms[np.argmin(logE)]-2**k} (valley check), max at n=2^k+{ms[np.argmax(logE)]-2**k}, x*/2^k={ (ms[np.argmax(logE)]+0.5)/2**k:.4f}")

print()
print("=== A2. Shell-mean of peaks vs kappa1 scale ===")
def log_g(x, kap):
    L = np.log(x)
    return -L*L/(2*a) - kap*L
for k in [9, 10, 11, 12, 13]:
    ms, logE, I = shell_peaks_and_integrals(k)
    E = np.exp(logE)
    meanE = E.mean()
    gval = np.exp(log_g(2.0**k * 1.4, kappa1))  # reference point; ratio series
    print(f"k={k:2d}: (mean E_n) / (A1 * g_k1 at shell) style ratio via sumE/int|f| = {E.sum()/I.sum():.4f}")

print()
print("=== B1. Discrete Parseval: sum_m P_n(m/2^n)^2 = 1 exactly ===")
def log_P(n, tt):
    out = np.zeros_like(tt)
    for j in range(n):
        out += np.log(np.abs(np.sin(np.pi * (2.0 ** j) * tt)))
    return out
for n in [6, 10, 14]:
    m = np.arange(1, 2**n, 2)  # even m give exact zeros
    vals = np.exp(2*log_P(n, m/2.0**n))
    print(f"n={n:2d}: sum over odd m of P_n^2 = {vals.sum():.12f} (even m contribute 0; total should be 1)")

print()
print("=== B2. Spectrum of L2 (collocation) ===")
def collocation_matrix(N, q):
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
L2m, xn = collocation_matrix(48, 2)
ev = np.linalg.eigvals(L2m)
ev = ev[np.argsort(-np.abs(ev))][:8]
print("top |eigenvalues| of L_2:", ", ".join(f"{e.real:+.12f}{e.imag:+.1e}i" if abs(e.imag)>1e-10 else f"{e.real:+.12f}" for e in ev))

print()
print("=== B3. A2 constant: direct shell L2 means vs spectral ===")
def W_kappa_vec(y, kap):
    return np.exp(log_abs_f(y)) * y**kap * np.exp(np.log(y)**2/(2*a))
# direct: (1/2^{k}) int_{2^k}^{2^{k+1}} (f/g_{k2})^2 dx
for k in [4, 6, 8, 10, 12, 14]:
    lo = 2**k
    ms = np.arange(lo, 2**(k+1))
    B = 4096; tot = 0.0
    for i in range(0, len(ms), B):
        mb = ms[i:i+B].astype(float)
        xg = (mb[:, None] + 0.5 + 0.5*gx24[None, :]).ravel()
        v = np.exp(2*(log_abs_f(xg) - log_g(xg, kappa2))).reshape(len(mb), -1)
        tot += float(np.sum((v @ gw24) * 0.5))
    print(f"k={k:2d}: shell mean of (f/g_k2)^2 = {tot/2**k:.10f}")
# spectral: rho2^{-n} int L2^n W2
wcc_N = 48
def clenshaw_curtis_weights(N):
    j = np.arange(N+1); v = np.zeros(N+1)
    for jj in range(N+1):
        s = 0.0
        for kk in range(0, N//2 + 1):
            ck = 1.0 if (kk==0 or 2*kk==N) else 2.0
            s += ck/(1-4*kk**2) * np.cos(2*kk*jj*np.pi/N)
        v[jj] = s
    w = 2.0/N * v; w[0] *= 0.5; w[N] *= 0.5
    return w/2.0
wcc = clenshaw_curtis_weights(wcc_N)
f2 = W_kappa_vec((xn + 1)/2, kappa2)**2
vec = f2.copy()
for n in range(1, 41):
    vec = (L2m @ vec) * 2.0
    if n in (6, 10, 14, 20, 40):
        print(f"spectral n={n:2d}: {np.dot(wcc, vec):.10f}")

print()
print("=== B4. L2 mantissa profile ===")
gx16, gw16 = leggauss(16)
n = 13
panels = 2**n
edges = np.arange(panels+1) / panels
mid = (edges[:-1]+edges[1:])/2; half = 0.5/panels
contrib = np.zeros(panels)
B = 8192
for i in range(0, panels, B):
    mm = mid[i:i+B]
    xx = (mm[:, None] + half*gx16[None, :]).ravel()
    v = (np.exp(2*log_P(n, xx)) * W_kappa_vec((xx+1)/2, kappa2)**2).reshape(-1, 16)
    contrib[i:i+B] = (v @ gw16) * half
cum = np.concatenate([[0.0], np.cumsum(contrib)]) * 2.0**n
denom = cum[-1]
pts = []
for zi in range(0, 41):
    z = zi/40.0
    idx = int(round(z * panels))
    Fz = cum[idx]/denom
    y = 1 + z
    P = (1 + Fz)/y
    pts.append((y, P))
print("L2 profile (y, P2(y)) step 0.025:")
print(" ".join(f"({y:.3f},{P:.6f})" for y, P in pts))
mn = min(p for _, p in pts); mx = max(p for _, p in pts)
print(f"min {mn:.6f}  max {mx:.6f}")

print()
print("=== B5. Plancherel/Poisson: 2 int_0^inf f^2 = 1/2 + sum f(m+1/2)^2 ===")
# direct integral to 2^14 (tail < 1e-80)
tot = 0.0
ms = np.arange(0, 2**14)
B = 8192
for i in range(0, len(ms), B):
    mb = ms[i:i+B].astype(float)
    xg = (mb[:, None] + 0.5 + 0.5*gx24[None, :]).ravel()
    xg = np.maximum(xg, 1e-12)
    v = np.exp(2*log_abs_f(xg)).reshape(len(mb), -1)
    tot += float(np.sum((v @ gw24) * 0.5))
direct = 2*tot
series = 0.5 + sum(float(np.exp(2*log_abs_f(np.array([m + 0.5]))[0])) for m in range(0, 40))
print(f"2 int f^2 = {direct:.15f}")
print(f"1/2 + sum f(m+1/2)^2 = {series:.15f}")
print(f"difference = {direct - series:.2e}")

print()
print("=== B6. kappa_q vs lognormal extrapolation ===")
print(" q     rho_q            kappa_q       lognormal kappa0 - q sigma^2/(2a)")
for q in [0.25, 0.5, 0.75, 1.0, 2.0, 3.0, 4.0]:
    Lq, _ = collocation_matrix(44, q)
    evq = np.linalg.eigvals(Lq)
    rq = float(np.max(evq.real[np.abs(evq.imag) < 1e-9]))
    kq = (LOGPI + a/2 - np.log(rq)/q) / a
    kLN = kappa0 - q*(np.pi**2/4)/(2*a)
    print(f"{q:4.2f}  {rq:.12f}  {kq:.9f}   {kLN:.9f}")
print(f"limits: q->0: kappa0 = {kappa0:.9f};  q->inf: kappainf = {kappainf:.9f}")
print(f"check (log rho_q)/(q a) -> -1 as q->0 (pressure slope):")
for q in [0.25, 0.5, 1.0]:
    Lq, _ = collocation_matrix(44, q)
    evq = np.linalg.eigvals(Lq)
    rq = float(np.max(evq.real[np.abs(evq.imag) < 1e-9]))
    print(f"  q={q}: (log rho_q)/(q a) = {np.log(rq)/(q*a):+.6f}")
