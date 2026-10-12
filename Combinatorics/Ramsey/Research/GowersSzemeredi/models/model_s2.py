import sys, math
sys.path.insert(0, r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\models')
import model_split_exact as M
cd = M.cover_log_deg(32, 2 ** 48, 16)
T = {l: cd[l] for l in range(1, 15)}
tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 5 * 2 ** (k - 1) + 3 * (k + 4) ** 2 + 2)
def thresholds(pc, pk, P):
    pDeg = lambda k: pc * k + pk
    mu0 = lambda k: max(4 * k + 13, pDeg(k)) + 2
    rho = lambda k: max(tDeg(k) + mu0(k) + 3, pDeg(k) + 1) + k
    dens = lambda k: rho(k) + 2 * tDeg(k) + 13
    exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, 4 * k + 18))
    pg = {0: 74, 1: 74}
    for k in range(2, 40):
        pg[k] = max(dens(k) + pg[k - 1] + P(k), exp_(k) + 6)
    return [next(d for d in range(4, 42) if all(pg[e - 2] + 1 <= 2 ** (e + c) for e in range(d, 42))) for c in (2, 3, 4)]
print('current (5k+21, k+19):', thresholds(5, 21, lambda k: k + 19))
print('budget 4k+15        :', thresholds(4, 15, lambda k: k + 19))
print('budget 3k+10        :', thresholds(3, 10, lambda k: k + 19))
print('step poly 0         :', thresholds(5, 21, lambda k: 0))
