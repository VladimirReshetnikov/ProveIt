import sys
sys.path.insert(0, r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\models')
import model_split_exact as M
def run(seedD):
    cd = M.cover_log_deg(32, seedD, 16)
    T = {l: cd[l] for l in range(1, 15)}
    tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 5 * 2 ** (k - 1) + 3 * (k + 4) ** 2 + 2)
    pDeg = lambda k: 5 * k + 21
    mu0 = lambda k: max(4 * k + 13, pDeg(k)) + 2
    rho = lambda k: max(tDeg(k) + mu0(k) + 3, pDeg(k) + 1) + k
    dens = lambda k: rho(k) + 2 * tDeg(k) + 13
    exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, 4 * k + 18))
    thr = lambda k: max(exp_(k) + 4, 5 * k + 30)
    pg = {0: 74, 1: 74}; gx = {0: 62, 1: 62}
    for k in range(2, 40):
        pg[k] = max(dens(k) + pg[k - 1] + k + 19, exp_(k) + 6)
        gx[k] = max(dens(k) + gx[k - 1] + 4 * (k + 3) ** 2 + 14, max(thr(k) + 3, k + 20))
    first = lambda f, lo, hi: next(d for d in range(lo, hi) if all(f(e) for e in range(d, hi)))
    ds = [first(lambda e: pg[e - 2] + 1 <= 2 ** (e + c), 4, 40) for c in (2, 3, 4)]
    Ls = [first(lambda e: gx[e - 4] + 2 * e + 14 <= 2 ** (e + c), 6, 42) for c in (0, 1, 2)]
    print('seed D2 = 2^%d' % (seedD.bit_length() - 1), 'table', [cd[l] for l in (2, 3, 4, 5)], ' 18.1 d+2/3/4 from', ds, ' 18.2 L+0/1/2 from', Ls)
run(2 ** 48); run(2 ** 46); run(2 ** 41)
