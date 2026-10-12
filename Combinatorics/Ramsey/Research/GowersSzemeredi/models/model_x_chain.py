T = {1: 17, 2: 49, 3: 85, 4: 136, 5: 210, 6: 326, 7: 524, 8: 881, 9: 1550, 10: 2841, 11: 5371, 12: 10375}
tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 5 * 2 ** (k - 1) + 3 * (k + 4) ** 2 + 2)
assert all(tDeg(k) <= tDeg(k + 1) for k in range(0, 60))
assert all(3 * (k + 4) ** 2 <= 3 * tDeg(k) + 5 * k + 37 for k in range(0, 60))
pDeg = lambda k: 5 * k + 21
mu0 = lambda k: max(4 * k + 13, pDeg(k)) + 2
muK = lambda k: 4 * k + 16
rho = lambda k: max(tDeg(k) + mu0(k) + 3, pDeg(k) + 1) + k
dens = lambda k: rho(k) + 2 * tDeg(k) + 13
exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, muK(k) + 2))
pg = {0: 74, 1: 74}
for k in range(2, 61):
    pg[k] = max(dens(k) + pg[k - 1] + 4 * (k + 3) ** 2 + 14, exp_(k) + 6)
for k in range(12, 22):
    x = 2 ** k
    print(k, 'pg', pg[k], ' d+2 fit', 16 * x - 1 - pg[k], ' inv16', 16 * x - pg[k] - 4 * k - 128)
# closed form k >= 13 with y = 2^(k-1): step <= mu + 15y + 9s + 4q + 6k + C
for k in range(13, 60):
    y, s, q = 2 ** (k - 1), (k + 4) ** 2, (k + 3) ** 2
    for mu in (0, 5, 10 ** 12):
        st = max(dens(k) + mu + 4 * q + 14, exp_(k) + 6)
        assert st <= mu + 15 * y + 9 * s + 4 * q + 6 * k + 59, (k, st - (mu + 15 * y + 9 * s + 4 * q + 6 * k))
print('closed form ok')
T = {1: 17, 2: 49, 3: 85, 4: 136, 5: 210, 6: 326, 7: 524, 8: 881, 9: 1550, 10: 2841, 11: 5371, 12: 10375}
tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 5 * 2 ** (k - 1) + 3 * (k + 4) ** 2 + 2)
pDeg = lambda k: 5 * k + 21
mu0 = lambda k: max(4 * k + 13, pDeg(k)) + 2
muK = lambda k: 4 * k + 16
rho = lambda k: max(tDeg(k) + mu0(k) + 3, pDeg(k) + 1) + k
dens = lambda k: rho(k) + 2 * tDeg(k) + 13
exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, muK(k) + 2))
for label, thr in (('L15.6 at 16*2^k', lambda k: max(exp_(k) + 4, 2 ** (k + 4) + 5 * k + 25)),
                   ('L15.6 polynomial', lambda k: max(exp_(k) + 4, 5 * k + 30))):
    gx = {0: 62, 1: 62}
    for k in range(2, 61):
        gx[k] = max(dens(k) + gx[k - 1] + 4 * (k + 3) ** 2 + 14, max(thr(k) + 3, k + 20))
    for c in (0, 1):
        Ls = [L for L in range(6, 65) if gx[L - 4] + 2 * L + 14 <= 2 ** (L + c)]
        print(label, 'L+%d from' % c, Ls[:3], 'contig' if Ls and Ls == list(range(Ls[0], 65)) else '')
    for k in range(14, 22):
        x = 2 ** k
        print('   ', k, 'L+0 fit', 16 * x - gx[k] - 2 * (k + 4) - 14, ' inv16', 16 * x - gx[k] - 4 * k - 128)
