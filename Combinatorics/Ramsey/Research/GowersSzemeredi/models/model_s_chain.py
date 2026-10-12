"""Exact model of the Section 18 chain at class degree cdeg(k), mirroring the Lean defs."""
import sys

def chain(cdeg, eta_fix, kmax=40):
    fixDegQ = lambda k: 2 ** (k + 4) + 7
    fixDeg = lambda k: 2 ** (k + 5) + 7
    mu0 = lambda k: max(2 ** (k + 4) + 1, fixDegQ(k)) + 2
    muK = lambda k: 2 ** (k + 5)
    def rho(k):
        r = max(cdeg(k) + mu0(k) + 3, fixDegQ(k) + 1) + k
        if eta_fix:   # the eta side condition fixDeg k <= rho + 2 mu_D + 9 forces rho up
            need = fixDeg(k) - 2 * (cdeg(k) + 1) - 9
            r = max(r, need)
        return r
    dens = lambda k: rho(k) + 2 * cdeg(k) + 13
    exp_ = lambda k: max(rho(k) + 2 * cdeg(k) + 9, max(rho(k) + cdeg(k) + k + 7, muK(k) + 2))
    thr = lambda k: max(exp_(k) + 4, 2 ** (k + 6) + 5)
    step = lambda k, mu: max(dens(k) + mu + 4 * (k + 3) ** 2 + 14, exp_(k) + 6)
    stepTx = lambda k, mu: max(dens(k) + mu + 4 * (k + 3) ** 2 + 14, max(thr(k) + 3, k + 20))
    pg = {0: 74, 1: 74}; gx = {0: 62, 1: 62}
    for k in range(2, kmax + 1):
        pg[k] = step(k, pg[k - 1]); gx[k] = stepTx(k, gx[k - 1])
    return pg, gx

def report(name, cdeg, eta_fix):
    pg, gx = chain(cdeg, eta_fix)
    print(f'== {name} (eta needs printed fixDeg: {eta_fix})')
    for c in (3, 4, 5, 6):
        ds = [d for d in range(4, 41) if d - 2 >= 2 and pg[d - 2] + 1 <= 2 ** (d + c)]
        Ls = [L for L in range(6, 43) if L - 4 >= 2 and gx[L - 4] + 2 * L + 14 <= 2 ** (L + c)]
        print(f'  18.1 d+{c}: from d={ds[0] if ds else None} (contiguous to 40: {ds == list(range(ds[0], 41)) if ds else None});'
              f'  18.2 L+{c}: from L={Ls[0] if Ls else None} (contig: {Ls == list(range(Ls[0], 43)) if Ls else None})')
    k = 30
    print('  step/2^k at k=30: poly', (pg[k] - pg[k - 1]) / 2 ** k, ' Tx', (gx[k] - gx[k - 1]) / 2 ** k,
          ' mu/2^k:', pg[k] / 2 ** k, gx[k] / 2 ** k)

qDeg = lambda k: 14 * 2 ** k + 3 * (k + 4) ** 2 + 2
sDeg = lambda k: 4 * 2 ** k + 3 * (k + 4) ** 2 + 32
report('Q (published)', qDeg, True)
report('S, eta at printed fixDeg', sDeg, True)
report('S, eta side condition 3(k+4)^2', sDeg, False)

if __name__ == '__main__':
    pg, gx = chain(sDeg, False, 60)
    # closed-form step bounds claimed for Lean
    for k in range(1, 60):
        x, s, q = 2 ** k, (k + 4) ** 2, (k + 3) ** 2
        for mu in (0, 1000, 10 ** 6):
            pass
    def step_ok(B, M, k0, fam, cap):
        """invariant mu_k + 4k + 128 <= M 2^k for k >= k0 (base by value, step by closed form)."""
        base = fam[k0] + 4 * k0 + 128 <= M * 2 ** k0
        bad = []
        for k in range(k0, 59):
            x2 = 2 ** (k + 1)
            # closed form at level k+1: mu + 28*2^(k+1) + 9 (k+5)^2 + 4 (k+4)^2 + (k+1) + 135, or cap*2^(k+1)+8
            lhs1 = M * 2 ** k - 4 * k - 128 + 28 * x2 + 9 * (k + 5) ** 2 + 4 * (k + 4) ** 2 + (k + 1) + 135
            lhs2 = cap * x2 + 8
            if max(lhs1, lhs2) + 4 * (k + 1) + 128 > M * x2: bad.append(k)
        return base, bad[:5]
    for M, k0 in ((64, 11), (128, 7)):
        print('poly M', M, 'k0', k0, step_ok(None, M, k0, pg, 32), ' value', pg[k0] + 4*k0 + 128, M * 2**k0)
    print('Tx M 128 k0 7', step_ok(None, 128, 7, gx, 64), gx[7] + 4*7+128, 128 * 2**7)
    # smallest k0 for each
    for M, fam, cap, nm in ((64, pg, 32, 'poly64'), (128, pg, 32, 'poly128'), (128, gx, 64, 'Tx128')):
        for k0 in range(2, 30):
            b, bad = step_ok(None, M, k0, fam, cap)
            if b and not bad: print(nm, 'invariant from k0 =', k0); break
