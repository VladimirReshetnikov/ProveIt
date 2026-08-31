"""Stage 5: fine profile grid for the report figure."""
import numpy as np
from numpy.polynomial.legendre import leggauss

LOG2 = np.log(2.0); LOGPI = np.log(np.pi); a = LOG2
rho1 = 0.661322602060565
kappa1 = (LOGPI + a/2 - np.log(rho1)) / a
gx16, gw16 = leggauss(16)

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
pts = []
for zi in range(0, 41):
    z = zi/40.0
    idx = int(round(z * panels))
    Fz = cum[idx]/denom
    y = 1 + z
    P = (1 + Fz)/y
    pts.append((y, P))
print("profile coordinates (y, P(y)) step 0.025:")
print(" ".join(f"({y:.3f},{P:.6f})" for y, P in pts))
mn = min(p for _, p in pts); mx = max(p for _, p in pts)
print(f"min {mn:.6f}  max {mx:.6f}")
# where
ymn = [y for y,p in pts if p == mn][0]; ymx = [y for y,p in pts if p == mx][0]
print(f"argmin y={ymn}, argmax y={ymx}")
