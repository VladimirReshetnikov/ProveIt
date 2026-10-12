import sys
sys.path.insert(0, r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\models')
import model_split_exact as M
cd = M.cover_log_deg(32, 2 ** 48, 24)
for top in (12, 14, 16, 18, 20):
    T = {l: cd[l] for l in range(1, top + 1)}
    tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 5 * 2 ** (k - 1) + 3 * (k + 4) ** 2 + 2)
    pDeg = lambda k: 5 * k + 21
    mu0 = lambda k: max(4 * k + 13, pDeg(k)) + 2
    rho = lambda k: max(tDeg(k) + mu0(k) + 3, pDeg(k) + 1) + k
    dens = lambda k: rho(k) + 2 * tDeg(k) + 13
    exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, 4 * k + 18))
    thr = lambda k: max(exp_(k) + 4, 5 * k + 30)
    pg = {0: 74, 1: 74}; gx = {0: 62, 1: 62}
    for k in range(2, 50):
        pg[k] = max(dens(k) + pg[k - 1] + 4 * (k + 3) ** 2 + 14, exp_(k) + 6)
        gx[k] = max(dens(k) + gx[k - 1] + 4 * (k + 3) ** 2 + 14, max(thr(k) + 3, k + 20))
    out = []
    for c in (0, 1, 2, 3, 4):
        ds = [d for d in range(4, 50) if pg[d - 2] + 1 <= 2 ** (d + c)]
        Ls = [L for L in range(6, 52) if gx[L - 4] + 2 * L + 14 <= 2 ** (L + c)]
        out.append('c=%d: d>=%s L>=%s' % (c, ds[0] if ds else '-', Ls[0] if Ls else '-'))
    print('table to', top, ' log2 D_top', cd[top], ' | ', ' ; '.join(out))
