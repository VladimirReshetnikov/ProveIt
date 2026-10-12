"""Exact split-class recursion under the Fejér inputs, and the envelope with the
actual per-dimension cover degrees (Notes L.16e, toward d + 5).

Mirrors, with exact integers:
* splitStepA k a = sCountN k a + sExpN k a            (Proofs16SplitStepBounds)
* splitStepDWith (fejerStepP k) (fejerStepT k) k a D   (Proofs16SplitFejerDegrees)
* splitPairWith seedA seedD: constant below dimension 2, then the steps;
and the class-cover degree uDeg_l = a_l + D_l + l + 1 (split_pair_fejer_le_uDeg23
proves it is at most 2^(23·2^l)). The envelope is that of
model_fejer_envelope_exact.py with the class term c·2^k replaced by
ceil(log2 uDeg_k).
"""
import math


def F(k): return 2 ** (3 * k + 7) * 2 ** (k + 4) * (k + 6)
def P(k): return 64 * F(k)
def T(k): return 22 * F(k) + 105


# family side (Proofs16SplitStepBounds)
def sQrN(k, a): return a * 2 ** k
def sSN(k, a): return sQrN(k, a) + 1
def sPbN(k, a): return a * (sSN(k, a) + 1)
def sCountN(k, a): return 1 + 2 * sSN(k, a) + 2 * sPbN(k, a)
def sErN(k, a): return a * 2 ** k
def sBqN(k, a): return a * 2 ** (k + 2)
def sLN(k, a): return sBqN(k, a) + (sErN(k, a) + a)
def sExpN(k, a): return 1 + sLN(k, a) + sPbN(k, a)
def splitStepA(k, a): return sCountN(k, a) + sExpN(k, a)


# parameter side with inputs (P, T) (Proofs16SplitFejerDegrees)
def wStepY(p, k, a, D): return a * (p + 1) + D * (p + k + 6)
def wSW(p, k, a, D): return wStepY(p, k, a, D) * 2 ** k + p + 8
def wPbW(p, k, a, D): return a * (p + wSW(p, k, a, D) + 1) + D * (p + 5)
def wCountW(p, k, a, D): return p + 1 + 2 * wSW(p, k, a, D) + 2 * wPbW(p, k, a, D)
def wEbW(p, a, D): return a * (p + 1) + D * (p + 6)
def wErW(p, k, a, D): return (wStepY(p, k, a, D) + 4) * 2 ** k
def wBqW(p, k, a, D): return 4 + (wEbW(p, a, D) + 1) * 2 ** (k + 2)
def wLW(p, k, a, D): return wBqW(p, k, a, D) + (wErW(p, k, a, D) + wEbW(p, a, D))
def wZW(p, t, a, D): return t + a + wEbW(p, a, D) + 7
def wExpW(p, t, k, a, D): return wZW(p, t, a, D) + wLW(p, k, a, D) + wPbW(p, k, a, D) + 6
def wThrDeg(p, D): return D * (p + 2) + p + 2


def splitStepD(k, a, D):
    p, t = P(k), T(k)
    return wCountW(p, k, a, D) + wExpW(p, t, k, a, D) + wThrDeg(p, D)


def split_pairs(seedA, seedD, kmax):
    out = {2: (seedA, seedD)}
    a, D = seedA, seedD
    for k in range(2, kmax):
        a, D = splitStepA(k, a), splitStepD(k, a, D)
        out[k + 1] = (a, D)
    return out


def log2ceil(n): return (n - 1).bit_length()


def cover_log_deg(seedA, seedD, kmax):
    pairs = split_pairs(seedA, seedD, kmax)
    res = {1: 17}                       # polyCoverAt_one_uniform_low: degree 2^17
    for l, (a, D) in pairs.items():
        res[l] = log2ceil(a + D + l + 1)
    return res


# envelope (model_fejer_envelope_exact.py with the class term replaced)
def envelope(cdeg, fixDeg, kmax, low=74):
    def tightMu0(k): return max(2 ** (k + 4) + 1, fixDeg(k)) + 2
    def genMuK(k): return 2 ** (k + 5)

    def rho(k): return max(cdeg[k] + tightMu0(k) + 3, fixDeg(k) + 1) + k
    def dens(k): return rho(k) + 2 * cdeg[k] + 13
    def exp_(k): return max(rho(k) + 2 * cdeg[k] + 9, max(rho(k) + cdeg[k] + k + 7, genMuK(k) + 2))
    mu = low
    out = {}
    for k in range(2, kmax):
        mu = max(dens(k) + mu + 4 * (k + 3) ** 2 + 14, exp_(k) + 6)
        out[k] = mu
    return out


def per_member_hypothesis():
    """Notes L.16h (unproved): per-relation remainder counts do not grow with
    the number of pieces sharing a partition, so the remainder's family
    exponents vanish (sQrN = sErN = 0) and the samples scale linearly in M."""
    global sQrN, sErN
    sQrN = lambda k, a: 0
    sErN = lambda k, a: 0


def per_degree_offsets(cd, fixDeg, kmax):
    env = envelope(cd, fixDeg, kmax)
    return {k + 2: min(c for c in range(0, 16) if env[k] + 1 <= 2 ** (k + 2 + c)) for k in env}


if __name__ == '__main__':
    import sys
    if '--per-member' in sys.argv:
        per_member_hypothesis()
        cd = cover_log_deg(2 ** 46, 2 ** 46, 16)
        for name, fx in (('printed fixDeg', lambda k: 2 ** (k + 5) + 7), ('Fejer fixDeg', lambda k: 5 * k + 22)):
            print(name, per_degree_offsets(cd, fx, 16))
        raise SystemExit
    KMAX = 13
    fix_printed = lambda k: 2 ** (k + 5) + 7
    fix_fejer = lambda k: 5 * k + 22
    for seed in (46, 43, 40, 36):
        cd = cover_log_deg(2 ** seed, 2 ** seed, KMAX)
        ratios = ', '.join(f'{l}:{cd[l] / 2 ** l:.2f}' for l in range(2, KMAX))
        print(f'seed 2^{seed}: log2(uDeg_l)/2^l = {ratios}')
        for name, fx in (('printed fixDeg', fix_printed), ('Fejer fixDeg', fix_fejer)):
            env = envelope(cd, fx, KMAX)
            fits5 = all(env[k] + 1 <= 2 ** (k + 2 + 5) for k in env)
            worst = max(env[k] / 2 ** k for k in env)
            print(f'   {name:15s}: envelope max {worst:6.1f}·2^k, d+5 at all d={min(env) + 2}..{max(env) + 2}: {fits5}')
