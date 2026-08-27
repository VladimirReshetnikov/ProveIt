"""Stage 4b: corrected L=1000 tail test (uniform initial points) + final constants."""
import numpy as np
from scipy.stats import norm
import mpmath as mp

print("=== Final constants at high precision ===")
mp.mp.dps = 25
rho1 = mp.mpf('0.661322602060565')
kappa1 = (mp.log(mp.pi) + mp.log(2)/2 - mp.log(rho1)) / mp.log(2)
print(f"kappa_1 from rho_1=0.661322602060565: {kappa1}")
kappa0 = mp.mpf(3)/2 + mp.log(mp.pi)/mp.log(2)
kappa2 = mp.log(2*mp.pi)/mp.log(2)
kappainf = (mp.log(mp.pi) + mp.log(2)/2 - mp.log(mp.sqrt(3)/2))/mp.log(2)
print(f"kappa_0 = {kappa0}")
print(f"kappa_2 = {kappa2}")
print(f"kappa_inf = {kappainf}")
print(f"pi/sqrt(2) = {mp.pi/mp.sqrt(2)}")
print(f"pi^2/4 = {mp.pi**2/4},  pi^2/12 = {mp.pi**2/12}")
# sensitivity of kappa1 to rho1 in last digit:
for r in ['0.66130', '0.66135']:
    k = (mp.log(mp.pi) + mp.log(2)/2 - mp.log(mp.mpf(r)))/mp.log(2)
    print(f"  rho={r} -> kappa={k}")

print()
print("=== Corrected tail test, L=1000, uniform initial points ===")
rng = np.random.default_rng(31)
L = 1000
M = 4_000_000
llog = np.log(np.log(L))
scale = np.sqrt(L * llog)
cs = np.array([1.5, 1.8, 2.0, 2.2214, 2.5, 2.8, 3.1416])
thr = cs * scale
cnt = np.zeros(len(thr), dtype=np.int64)
var_acc = 0.0; mean_acc = 0.0; tot = 0
batch = 500_000
for b in range(M // batch):
    q = (rng.integers(2**60, 2**61, size=batch, dtype=np.uint64) << np.uint64(1)) + np.uint64(1)
    p = rng.integers(np.uint64(1), q, dtype=np.uint64)  # uniform in [1, q)
    S = np.zeros(batch)
    for j in range(L):
        t = p.astype(np.float64) / q.astype(np.float64)
        S += np.log(np.abs(2.0 * np.sin(np.pi * t)))
        p = (p << np.uint64(1)) % q
    ok = np.isfinite(S)
    S = S[ok]
    tot += len(S)
    mean_acc += S.sum(); var_acc += (S**2).sum()
    for i, th in enumerate(thr):
        cnt[i] += int(np.sum(S > th))
mean = mean_acc / tot
var = var_acc / tot - mean**2
print(f"L={L}, samples={tot}")
print(f"mean S_L = {mean:.4f} (predict 0); Var(S_L) = {var:.2f}")
print(f"  prediction sigma^2=pi^2/4: {L*np.pi**2/4 - np.pi**2/3:.2f}")
print(f"  prediction sigma^2=pi^2/2: {L*np.pi**2/2 - 2*np.pi**2/3:.2f}")
print()
print(" c        threshold  empirical P             Gauss(pi/2)     Gauss(pi/sqrt2)")
for i, cft in enumerate(cs):
    th = thr[i]
    emp = cnt[i] / tot
    g1 = norm.sf(th / (np.pi/2 * np.sqrt(L)))
    g2 = norm.sf(th / (np.pi/np.sqrt(2) * np.sqrt(L)))
    print(f"{cft:7.4f}  {th:9.2f}  {emp:.4e} ({cnt[i]:>8d})   {g1:.4e}     {g2:.4e}")
