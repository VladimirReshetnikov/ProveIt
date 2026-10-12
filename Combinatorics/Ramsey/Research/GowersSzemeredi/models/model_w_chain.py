T = {1: 17, 2: 49, 3: 85, 4: 136, 5: 210, 6: 326, 7: 524, 8: 881, 9: 1550, 10: 2841, 11: 5371, 12: 10375}
tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 4 * 2 ** k + 3 * (k + 4) ** 2 + 32)
pDeg = lambda k: 5 * k + 21
mu0 = lambda k: max(4 * k + 13, pDeg(k)) + 2
muK = lambda k: 4 * k + 16
rho = lambda k: max(tDeg(k) + mu0(k) + 3, pDeg(k) + 1) + k
dens = lambda k: rho(k) + 2 * tDeg(k) + 13
exp_ = lambda k: max(rho(k) + 2 * tDeg(k) + 9, max(rho(k) + tDeg(k) + k + 7, muK(k) + 2))
thr = lambda k: max(exp_(k) + 4, 2 ** (k + 4) + 5 * k + 25)
pg = {0: 74, 1: 74}; gx = {0: 62, 1: 62}
for k in range(2, 41):
    pg[k] = max(dens(k) + pg[k - 1] + 4 * (k + 3) ** 2 + 14, exp_(k) + 6)
    gx[k] = max(dens(k) + gx[k - 1] + 4 * (k + 3) ** 2 + 14, max(thr(k) + 3, k + 20))
assert all(3 * (k + 4) ** 2 <= 3 * tDeg(k) + 5 * k + 37 for k in range(0, 60))
for k in range(2, 16):
    x = 2 ** k
    print(k, 'pg', pg[k], ' d+3 m', 32 * x - 1 - pg[k], ' d+4 m', 64 * x - 1 - pg[k], ' d+5 m', 128 * x - 1 - pg[k],
          '| gx', gx[k], ' L+1 m', 32 * x - gx[k] - 2 * (k + 4) - 14, ' L+2 m', 64 * x - gx[k] - 2 * (k + 4) - 14,
          ' L+3 m', 128 * x - gx[k] - 2 * (k + 4) - 14, '| inv32 pg', 32 * x - pg[k] - 4 * k - 128, ' gx', 32 * x - gx[k] - 4 * k - 128)
for k in range(13, 40):
    x, s, q = 2 ** k, (k + 4) ** 2, (k + 3) ** 2
    for mu in (0, 7, 10 ** 9):
        st = max(dens(k) + mu + 4 * q + 14, exp_(k) + 6)
        assert st <= mu + 12 * x + 9 * s + 4 * q + 6 * k + 149, k
        stx = max(dens(k) + mu + 4 * q + 14, max(thr(k) + 3, k + 20))
        assert stx <= max(mu + 12 * x + 9 * s + 4 * q + 6 * k + 149, 16 * x + 5 * k + 28), k
print('closed forms ok')
