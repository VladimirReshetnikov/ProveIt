"""Stage 6b: supplements — k=14 peak ratio, L1 subleading spectrum, RMS error alternation."""
import numpy as np
from numpy.polynomial.legendre import leggauss

LOG2 = np.log(2.0); LOGPI = np.log(np.pi); a = LOG2
rho1 = 0.661322602060565
kappa2 = np.log(2*np.pi)/a
gx24, gw24 = leggauss(24)

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

def log_g(x, kap):
    L = np.log(x)
    return -L*L/(2*a) - kap*L

print("=== k=14 peak/integral ratio ===")
uu = np.linspace(0.004, 0.996, 96)
offs = (1 - np.cos(np.pi * uu)) / 2
k = 14
ms = np.arange(2**k, 2**(k+1))
sumE = 0.0; sumI = 0.0
B = 2048
for i in range(0, len(ms), B):
    mb = ms[i:i+B].astype(float)
    xx = (mb[:, None] + offs[None, :]).ravel()
    lv = log_abs_f(xx).reshape(len(mb), -1)
    j = np.argmax(lv, axis=1); j = np.clip(j, 1, len(offs)-2)
    idx = np.arange(len(mb))
    t0 = offs[j-1]; t1 = offs[j]; t2 = offs[j+1]
    f0 = lv[idx, j-1]; f1 = lv[idx, j]; f2 = lv[idx, j+1]
    d1 = t1-t0; d2 = t2-t1
    A_ = (f0*d2 - f1*(d1+d2) + f2*d1)*2/(d1*d2*(d1+d2))
    B_ = (f2 - f0 - A_/2*(t2**2 - t0**2))/(t2 - t0)
    tstar = np.clip(np.where(A_ < 0, -B_/A_, t1), t0, t2)
    sumE += float(np.exp(np.maximum(log_abs_f(mb + tstar), f1)).sum())
    xg = (mb[:, None] + 0.5 + 0.5*gx24[None, :]).ravel()
    v = np.exp(log_abs_f(xg)).reshape(len(mb), -1)
    sumI += float(np.sum((v @ gw24) * 0.5))
print(f"k=14: sum(E_n)/int_shell|f| = {sumE/sumI:.5f}")

print()
print("=== L1 subleading spectrum ===")
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
        ii = np.where(exact)
        M[ii[0], ii[1]] = 1.0
        return M
    A = interp_matrix(x / 2); Bm = interp_matrix((x + 1) / 2)
    L = 0.5 * (np.sin(np.pi*x/2)[:, None]**q * A + np.cos(np.pi*x/2)[:, None]**q * Bm)
    return L, x
for N in [40, 48]:
    L1m, _ = collocation_matrix(N, 1)
    ev = np.linalg.eigvals(L1m)
    ev = ev[np.argsort(-np.abs(ev))][:4]
    print(f"N={N}: top L_1 eigenvalues:", ", ".join(f"{e.real:+.10f}{e.imag:+.1e}i" if abs(e.imag)>1e-9 else f"{e.real:+.10f}" for e in ev))

print()
print("=== RMS shell-mean at odd k (alternation check) and A2 ===")
for k in [5, 7, 9, 11, 13]:
    lo = 2**k
    ms = np.arange(lo, 2**(k+1))
    B = 4096; tot = 0.0
    for i in range(0, len(ms), B):
        mb = ms[i:i+B].astype(float)
        xg = (mb[:, None] + 0.5 + 0.5*gx24[None, :]).ravel()
        v = np.exp(2*(log_abs_f(xg) - log_g(xg, kappa2))).reshape(len(mb), -1)
        tot += float(np.sum((v @ gw24) * 0.5))
    print(f"k={k:2d}: shell mean of (f/g_k2)^2 = {tot/2**k:.10f}")
A2sq = 0.0106108372
print(f"A2 = sqrt({A2sq}) = {np.sqrt(A2sq):.9f}")
print(f"1.9237 * A1 = {1.9237*0.0912661241:.7f}")
