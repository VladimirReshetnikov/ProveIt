T = {1: 17, 2: 49, 3: 85, 4: 136, 5: 210, 6: 326, 7: 524, 8: 881, 9: 1550, 10: 2841, 11: 5371, 12: 10375}
tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 4 * 2 ** k + 3 * (k + 4) ** 2 + 32)
fixDegQ = lambda k: 2 ** (max(k - 1, 0) + 5) + 7
mu0 = lambda k: max(2 ** (k + 4) + 1, fixDegQ(k)) + 2
muK = lambda k: 2 ** (k + 5)
rho = lambda k: max(tDeg(k) + mu0(k) + 3, fixDegQ(k) + 1) + k
dens = lambda k: rho(k) + 2 * tDeg(k) + 13
exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, muK(k) + 2))
thrT = lambda k: max(exp_(k) + 4, 2 ** (k + 6) + 5)
thrU = lambda k: max(exp_(k) + 4, 2 ** (k + 4) + 5 * k + 25)
def gx(thr, kmax=40):
    g = {0: 62, 1: 62}
    for k in range(2, kmax + 1):
        g[k] = max(dens(k) + g[k - 1] + 4 * (k + 3) ** 2 + 14, max(thr(k) + 3, k + 20))
    return g
for name, thr in (('T', thrT), ('U', thrU)):
    g = gx(thr)
    for c in (2, 3):
        Ls = [L for L in range(6, 45) if g[L - 4] + 2 * L + 14 <= 2 ** (L + c)]
        print(name, 'L+%d at' % c, Ls[:8], '...', 'contiguous to 44' if Ls and Ls == list(range(Ls[0], 45)) else Ls)
    print(name, 'ratios', [round(g[k] / 2 ** k, 1) for k in range(2, 16)])
g = gx(thrU, 30)
for k in range(2, 16):
    x = 2 ** k
    print(k, g[k], 'L+2 margin', 64 * x - g[k] - 2 * (k + 4) - 14, ' inv64', 64 * x - g[k] - 4 * k - 128)
# closed form check for k >= 13: step <= max(mu + 28x + 9s + 4q + k + 135, 32x + 9)
for k in range(13, 40):
    x, s, q = 2 ** k, (k + 4) ** 2, (k + 3) ** 2
    for mu in (0, 10, 10 ** 9):
        st = max(dens(k) + mu + 4 * q + 14, max(thrU(k) + 3, k + 20))
        assert st <= max(mu + 28 * x + 9 * s + 4 * q + k + 135, 32 * x + 9), (k, mu)
        assert st >= 32 * x + 9
print('closed form ok')
