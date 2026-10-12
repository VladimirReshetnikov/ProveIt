"""Exact mirror of the Fejér Section 18 envelopes (Notes L.16d).

The definitions are those of the Lean modules Proofs18CoverDensityFejer /
Proofs18CoverExponentsFejer (class degree 23·2^k) and of the tight base
budget (tightMu0) of Proofs18CoverTightBase:
  rhoDegF k μ0   = max(23·2^k + μ0 + 3, fixDeg k + 1) + k
  densDegF k μ0  = rhoDegF + 2·(23·2^k) + 13
  expDegF        = max(rhoDegF + 2·23·2^k + 9, max(rhoDegF + 23·2^k + k + 7, μK + 2))
  threshDegF     = max(expDegF + 4, 2^(k+6) + 5)
  envStepF       = max(densDegF + μ + 4(k+3)² + 14, expDegF + 6)          (Theorem 18.1)
  envStepFTx     = max(densDegF + μ + 4(k+3)² + 14, max(threshDegF + 3, k + 20))   (18.2)
with μ0 = tightMu0 k = max(2^(k+4)+1, 2^(k+5)+7) + 2 and μK = genMuK k = 2^(k+5).
Prints the envelopes against the budgets of Theorem 18.1 at d + c
(μ + 1 ≤ 2^(d+c), d = k + 2) and Theorem 18.2 at L + c
(μ + 2L + 14 ≤ 2^(L+c), L = k + 4).
"""


def fixDeg(k): return 2 ** (k + 5) + 7
def tightMu0(k): return max(2 ** (k + 4) + 1, fixDeg(k)) + 2
def genMuK(k): return 2 ** (k + 5)


def rhoDeg(k, m0, c): return max(c * 2 ** k + m0 + 3, fixDeg(k) + 1) + k
def densDeg(k, m0, c): return rhoDeg(k, m0, c) + 2 * (c * 2 ** k) + 13


def expDeg(k, m0, mK, c):
    r = rhoDeg(k, m0, c)
    return max(r + 2 * (c * 2 ** k) + 9, max(r + c * 2 ** k + k + 7, mK + 2))


def threshDeg(k, m0, mK, c): return max(expDeg(k, m0, mK, c) + 4, 2 ** (k + 6) + 5)


def envStep(k, mu, c):
    m0, mK = tightMu0(k), genMuK(k)
    return max(densDeg(k, m0, c) + mu + 4 * (k + 3) ** 2 + 14, expDeg(k, m0, mK, c) + 6)


def envStepTx(k, mu, c):
    m0, mK = tightMu0(k), genMuK(k)
    return max(densDeg(k, m0, c) + mu + 4 * (k + 3) ** 2 + 14, max(threshDeg(k, m0, mK, c) + 3, k + 20))


def poly(k, c):
    return 74 if k <= 1 else envStep(k, poly(k - 1, c), c)


def genX(k, c):
    return 62 if k <= 1 else envStepTx(k, genX(k - 1, c), c)


if __name__ == '__main__':
    for c in (68, 23):
        print(f'class constant {c}')
        for k in range(2, 14):
            p, g = poly(k, c), genX(k, c)
            d, L = k + 2, k + 4
            print(f'  k={k:2d} poly={p:9d} ratio={p / 2 ** k:7.2f} d+6 fits={p + 1 <= 2 ** (d + 6)}'
                  f'  genX={g:9d} ratio={g / 2 ** k:7.2f} L+4 fits={g + 2 * L + 14 <= 2 ** (L + 4)}')
