"""Stage 1: core verifications for the sinc-product decay analysis.

f(x) = prod_{h>=0} sinc(pi x / 2^h),  sinc z = sin z / z.
"""
import numpy as np

LOG2 = np.log(2.0)
LOGPI = np.log(np.pi)

def log_abs_f(x):
    """log|f(x)| for array/scalar x>0, vectorized; -inf at zeros."""
    x = np.asarray(x, dtype=float)
    H = int(np.ceil(np.log2(np.pi * float(np.max(x))) )) + 30
    out = np.zeros_like(x)
    for h in range(H + 1):
        u = np.pi * x / (2.0 ** h)
        small = u < 1e-4
        t = np.where(small, 1.0, u)  # dummy to avoid warnings
        with np.errstate(divide='ignore', invalid='ignore'):
            big_term = np.log(np.abs(np.sin(t))) - np.log(t)
        small_term = -u * u / 6.0 - u ** 4 / 180.0
        out += np.where(small, small_term, big_term)
    return out

def f_val(x):
    """f(x) with sign, via direct product (for sanity at small x)."""
    x = np.asarray(x, dtype=float)
    H = int(np.ceil(np.log2(np.pi * float(np.max(np.abs(x))) + 1))) + 40
    out = np.ones_like(x)
    for h in range(H + 1):
        u = np.pi * x / (2.0 ** h)
        s = np.where(np.abs(u) < 1e-8, 1.0 - u*u/6.0, np.sin(u) / np.where(u == 0, 1, u))
        out *= s
    return out

print("=== A. Sanity: exact dyadic factorization (solution 3 Thm 3.1 / solution 4 Thm 2.3) ===")
# |f(2^k y)| = 2^{-k(k+1)/2} (pi y)^{-(k+1)} H(y) P_{k+1}(y-1),  1<=y<2
# H(y) = prod_{m>=1} |sinc(pi y/2^m)|
def log_H(y):
    y = np.asarray(y, dtype=float)
    out = np.zeros_like(y)
    for m in range(1, 60):
        u = np.pi * y / 2.0 ** m
        small = u < 1e-4
        t = np.where(small, 1.0, u)
        with np.errstate(divide='ignore'):
            big = np.log(np.abs(np.sin(t) / t))
        out += np.where(small, -u*u/6 - u**4/180, big)
    return out

def log_P(n, t):
    """log prod_{j=0}^{n-1} |sin(pi 2^j t)| -- ONLY reliable for n <= ~40 in doubles."""
    t = np.asarray(t, dtype=float)
    out = np.zeros_like(t)
    for j in range(n):
        out += np.log(np.abs(np.sin(np.pi * (2.0 ** j) * t)))
    return out

rng = np.random.default_rng(1)
ys = 1 + rng.random(5)
for k in [3, 7, 12]:
    lhs = log_abs_f(2.0 ** k * ys)
    rhs = (-k*(k+1)/2*LOG2 - (k+1)*(LOGPI + np.log(ys)) + log_H(ys) + log_P(k+1, ys - 1))
    print(f"k={k}: max |lhs-rhs| = {np.max(np.abs(lhs - rhs)):.2e}")

print()
print("=== B. I_2(n) = int_0^1 P_n(t)^2 dt = 2^{-n} exactly (sol 3 eq L2-exact / sol 4) ===")
from numpy.polynomial.legendre import leggauss
gx16, gw16 = leggauss(16)
def integrate_Pn_pow(n, power, weight=None):
    """int_0^1 P_n(t)^power * weight(t) dt via 2^n panels x 16pt Gauss."""
    panels = 2 ** n
    a = np.arange(panels) / panels
    # nodes: shape (panels, 16)
    tt = a[:, None] + (gx16[None, :] + 1) / (2 * panels)
    tt = tt.ravel()
    v = np.exp(power * log_P(n, tt))
    if weight is not None:
        v = v * weight(tt)
    v = v.reshape(panels, 16)
    return float(np.sum(v @ gw16) / (2 * panels))

for n in [2, 5, 8, 11]:
    val = integrate_Pn_pow(n, 2.0)
    print(f"n={n:2d}: I_2 = {val:.12e}, 2^-n = {2.0**-n:.12e}, ratio = {val * 2.0**n:.12f}")

print()
print("=== C. I_1(n) = int_0^1 P_n dt, ratios -> rho_1 (Perron root) ===")
I1 = {}
for n in range(1, 15):
    I1[n] = integrate_Pn_pow(n, 1.0)
for n in range(2, 15):
    print(f"n={n:2d}: I_1 = {I1[n]:.10e}, ratio I(n)/I(n-1) = {I1[n]/I1[n-1]:.12f}")

print()
print("=== D. Chebyshev collocation for rho_q (transfer operator L_q) ===")
def collocation_matrix(N, q):
    j = np.arange(N + 1)
    x = (1 - np.cos(np.pi * j / N)) / 2  # Chebyshev-Lobatto on [0,1]
    # barycentric weights for Chebyshev-Lobatto
    w = np.ones(N + 1); w[0] = 0.5; w[N] = 0.5; w *= (-1.0) ** j
    def interp_matrix(pts):
        # M[i,k] such that p(pts[i]) = sum_k M[i,k] f(x_k)
        D = pts[:, None] - x[None, :]
        exact = np.abs(D) < 1e-14
        D = np.where(exact, 1.0, D)
        C = w[None, :] / D
        M = C / np.sum(C, axis=1)[:, None]
        M[np.any(exact, axis=1)] = 0.0
        idx = np.where(exact)
        M[idx[0], idx[1]] = 1.0
        return M
    A = interp_matrix(x / 2)
    B = interp_matrix((x + 1) / 2)
    s1 = np.sin(np.pi * x / 2) ** q
    c1 = np.cos(np.pi * x / 2) ** q
    L = 0.5 * (s1[:, None] * A + c1[:, None] * B)
    return L, x

for q in [1, 2, 3, 4]:
    vals = []
    for N in [16, 24, 32, 40]:
        L, xn = collocation_matrix(N, q)
        ev = np.linalg.eigvals(L)
        rho = float(np.max(ev.real[np.abs(ev.imag) < 1e-8]))
        vals.append(rho)
    print(f"q={q}: rho (N=16,24,32,40) = " + ", ".join(f"{v:.15f}" for v in vals))

rho1 = vals_q1 = None
L40, x40 = collocation_matrix(40, 1)
ev = np.linalg.eigvals(L40)
rho1 = float(np.max(ev.real[np.abs(ev.imag) < 1e-8]))
a = LOG2
kappa1 = (LOGPI + a / 2 - np.log(rho1)) / a
kappa0 = 1.5 + LOGPI / a
kappa2 = np.log(2 * np.pi) / a
kappainf = (LOGPI + a / 2 - np.log(np.sqrt(3) / 2)) / a
print()
print(f"rho_1     = {rho1:.15f}   (claimed 0.661322602060565)")
print(f"kappa_1   = {kappa1:.15f} (claimed 2.748070014871335)")
print(f"kappa_0   = {kappa0:.15f} (claimed 3.151496129472319)")
print(f"kappa_2   = {kappa2:.15f} (claimed 2.651496129472318)")
print(f"kappa_inf = {kappainf:.15f} (claimed 2.359014879111741)")

print()
print("=== E. Constants: H(1) = f-tail at 1 = Phi(1/2); exact ray identities ===")
import mpmath as mp
mp.mp.dps = 30
H1 = mp.nprod(lambda r: mp.sinc(mp.pi / 2**r), [1, mp.inf])
print(f"H(1) = prod sinc(pi/2^r) = {H1}  (sol2/sol4 claim 0.55377127588881009534)")
# f(1/2) check equals H(1):
print(f"log_abs_f(0.5) = {log_abs_f(np.array([0.5]))[0]:.15f}, log H1 = {float(mp.log(H1)):.15f}")

# Exact slow ray (sol 1 Prop, y=4/3): |f(2^k*4/3)| = |f(4/3)| (3sqrt3/(8pi))^k 2^{-k(k+1)/2}
k = 6
lhs = log_abs_f(np.array([2.0**k * 4/3]))[0]
rhs = log_abs_f(np.array([4/3]))[0] + k*np.log(3*np.sqrt(3)/(8*np.pi)) - k*(k+1)/2*LOG2
print(f"slow-ray identity k={k}: lhs={lhs:.12f} rhs={rhs:.12f} diff={lhs-rhs:.2e}")

# sol 4 exact peak ray at 2^n * 2/3 with C* = W_kappainf(2/3)
def W_kappa(y, kap):
    return np.exp(log_abs_f(np.array([y]))[0]) * y**kap * np.exp(np.log(y)**2/(2*a))
Cstar = W_kappa(2/3, kappainf)
print(f"W_kappainf(2/3) = {Cstar:.15f} (sol4 claims 0.139129774734829)")
n = 9
x = 2.0**n * 2/3
lhs = log_abs_f(np.array([x]))[0]
rhs = np.log(Cstar) - np.log(x)**2/(2*a) - kappainf*np.log(x)
print(f"peak-ray identity n={n}: lhs={lhs:.12f} rhs={rhs:.12f} diff={lhs-rhs:.2e}")

print()
print("=== F. Variance of S_N = sum_{j<N} log|2 sin(pi T^j t)| : test sigma^2 = pi^2/4 ===")
# Prediction: Var(S_N) = N*pi^2/4 - pi^2/3 + o(1)   [Green-Kubo with covariances pi^2/(12*2^k)]
N = 40
M = 200000
t0 = rng.random(M)  # random doubles; doubling map exact on 53-bit mantissas for ~50 steps
S = np.zeros(M)
t = t0.copy()
for j in range(N):
    S += np.log(np.abs(2 * np.sin(np.pi * t)))
    t = (2 * t) % 1.0
mean_S = S.mean(); var_S = S.var()
pred = N * np.pi**2 / 4 - np.pi**2 / 3
print(f"N={N}, M={M}: mean S_N = {mean_S:.4f} (predict ~0)")
print(f"Var(S_N) = {var_S:.3f};  prediction N*pi^2/4 - pi^2/3 = {pred:.3f};  N*pi^2/2 - .. = {N*np.pi**2/2 - 2*np.pi**2/3:.1f}")
print(f"=> per-step variance estimate {var_S/N + np.pi**2/(3*N):.4f} vs pi^2/4 = {np.pi**2/4:.4f} vs pi^2/2 = {np.pi**2/2:.4f}")
