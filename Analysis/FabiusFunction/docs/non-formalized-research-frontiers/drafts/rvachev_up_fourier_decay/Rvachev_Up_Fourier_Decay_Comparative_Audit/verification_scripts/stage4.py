"""Stage 4: LIL-scale tail test at L=1000 with exact rational orbits (p -> 2p mod q)."""
import numpy as np
from scipy.stats import norm

rng = np.random.default_rng(23)
L = 1000
M = 4_000_000
llog = np.log(np.log(L))
scale = np.sqrt(L * llog)
sig_true = np.pi / 2            # CLT sigma (verified numerically)
sig_alt = np.pi / np.sqrt(2)    # sigma implied by AHL's printed constant pi

cs = np.array([1.5, 1.8, 2.0, 2.2214, 2.5, 2.8, 3.1416])
thr = cs * scale
cnt = np.zeros(len(thr), dtype=np.int64)
var_acc = 0.0; mean_acc = 0.0; tot = 0
batch = 1_000_000
for b in range(M // batch):
    # independent odd moduli ~2^61 and random residues
    q = (rng.integers(2**60, 2**61, size=batch, dtype=np.uint64) << np.uint64(1)) + np.uint64(1)
    p = rng.integers(1, 2**59, size=batch, dtype=np.uint64) % q
    p = np.maximum(p, np.uint64(1))
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
print(f"mean S_L = {mean:.4f} (predict ~0); Var(S_L) = {var:.2f}")
print(f"  predictions: N pi^2/4 - pi^2/3 = {L*np.pi**2/4 - np.pi**2/3:.2f}; N pi^2/2 - .. = {L*np.pi**2/2 - 2*np.pi**2/3:.2f}")
print(f"deterministic cap L log sqrt3 = {L*np.log(np.sqrt(3.0)):.1f}; sqrt(L llog L) = {scale:.2f}")
print()
print(" c        threshold  empirical P             Gauss(sigma=pi/2)     Gauss(sigma=pi/sqrt2)")
for i, cft in enumerate(cs):
    th = thr[i]
    emp = cnt[i] / tot
    g1 = norm.sf(th / (sig_true * np.sqrt(L)))
    g2 = norm.sf(th / (sig_alt * np.sqrt(L)))
    print(f"{cft:7.4f}  {th:9.2f}  {emp:.4e}  ({cnt[i]:>8d})   {g1:.4e}          {g2:.4e}")
