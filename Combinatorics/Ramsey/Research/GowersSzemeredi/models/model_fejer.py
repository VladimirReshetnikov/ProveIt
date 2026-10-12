"""What a Fejer-kernel Lemma 15.5 would buy (notes L.16, model only).

Mirrors the split-class recursion of Proofs16SplitStepBounds exactly
(splitStepA / splitStepD over sCountN, sExpN, sCountW, sExpW, stepThrDeg),
with the theta_1-driven inputs as parameters:
  stepP k = 64 * E1(k)          (printed E1 = 2^(2^(k+5)))
  stepT k = E1(k)^2             (Bohr exponent, printed 2^(2^(k+6)))
  seed    = 16 * stepT(1)^(1/2)... printed 2^132 (= 2^(128+4))
  fixDeg k = log2 E1(k) + 7
Printed:  E1 = 2^(2^(k+5)).
Fejer:    S' = 2^(k+4) * (1 + ceil((k+5)/2)),  E1' = 2^(3k+7) * S'
          (Lemma 15.6 multiplies the selection exponent by <= 2^(3k+7)).
Then the step cost (in units of 2^k) is
  cover degree + mu0 + 2 * slice degree,
with slice degree = cover degree (both are the class degree), and
mu0 = max(tightMuV, fixDeg) + 2, tightMuV = 2^(k+4) + 1 (Section 5, unchanged).
Envelope: the model_mu0 recursion with 68 replaced by the class constant.
"""
import math
import sys


def log2(n):
    return n.bit_length() - 1


def run_split(stepP, stepT, seed, kmax):
    def sStepY(k, a, D): return a * (stepP(k) + 1) + D * (stepP(k) + k + 6)
    def sSN(k, a): return a * 2 ** k + 1
    def sSW(k, a, D): return sStepY(k, a, D) * 2 ** k + stepP(k) + 8
    def sPbN(k, a): return a * (sSN(k, a) + 1)
    def sPbW(k, a, D): return a * (stepP(k) + sSW(k, a, D) + 1) + D * (stepP(k) + 5)
    def sCountN(k, a): return 1 + 2 * sSN(k, a) + 2 * sPbN(k, a)
    def sCountW(k, a, D): return stepP(k) + 1 + 2 * sSW(k, a, D) + 2 * sPbW(k, a, D)
    def sEbW(k, a, D): return a * (stepP(k) + 1) + D * (stepP(k) + 6)
    def sLN(k, a): return a * 2 ** (k + 2) + (a * 2 ** k + a)
    def sLW(k, a, D): return 4 + (sEbW(k, a, D) + 1) * 2 ** (k + 2) + ((sStepY(k, a, D) + 4) * 2 ** k + sEbW(k, a, D))
    def sZW(k, a, D): return stepT(k) + a + sEbW(k, a, D) + 7
    def sExpN(k, a): return 1 + sLN(k, a) + sPbN(k, a)
    def sExpW(k, a, D): return sZW(k, a, D) + sLW(k, a, D) + sPbW(k, a, D) + 6
    def stepThrDeg(k, D): return D * (stepP(k) + 2) + stepP(k) + 2
    a, D = seed, seed
    out = {2: (a, D)}
    for k in range(2, kmax):
        a, D = sCountN(k, a) + sExpN(k, a), sCountW(k, a, D) + sExpW(k, a, D) + stepThrDeg(k, D)
        out[k + 1] = (a, D)
    return out


def envelope(cls, fixDeg, kmax):
    """model_mu0 recursion with class constant cls(k) (log2 of the cover degree / 2^k)."""
    mu = 74; muT = 62; rows = []
    for k in range(2, kmax):
        cD = math.ceil(cls(k) * 2 ** k)
        m0 = max(2 ** (k + 4) + 1, fixDeg(k)) + 2; mK = 2 ** (k + 5)
        rho = max(cD + m0 + 3, fixDeg(k) + 1) + k
        dens = rho + 2 * cD + 13
        exp_ = max(rho + 2 * cD + 9, rho + cD + k + 7, mK + 2)
        thr = max(exp_ + 4, 2 ** (k + 6) + 5)
        mu = max(dens + mu + 4 * (k + 3) ** 2 + 14, exp_ + 6)
        muT = max(dens + muT + 4 * (k + 3) ** 2 + 14, thr + 3)
        d = k + 2; L = k + 4
        c1 = max(0, math.ceil(math.log2(mu + 1)) - d)
        c2 = max(0, math.ceil(math.log2(muT + 2 * L + 14)) - L)
        rows.append((k, cD / 2 ** k, (mu + 1) / 2 ** k, c1, c2))
    return rows


KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12

printed = dict(
    E1=lambda k: 2 ** (2 ** (k + 5)),
)
S_fejer = lambda k: 2 ** (k + 4) * (1 + math.ceil((k + 5) / 2))
fejer = dict(
    E1=lambda k: 2 ** (3 * k + 7) * S_fejer(k),
)

for name, P in (('printed', printed), ('fejer', fejer)):
    E1 = P['E1']
    if name == 'printed':
        stepP = lambda k: 2 ** (2 ** (k + 5) + 6)
        stepT = lambda k: 2 ** (2 ** (k + 6))
        seed = 2 ** 132
        fixDeg = lambda k: 2 ** (k + 5) + 7
    else:
        stepP = lambda k, E1=E1: 64 * E1(k)
        stepT = lambda k, E1=E1: E1(k) ** 2
        seed = 2 ** (log2(E1(1) ** 2) + 4)
        fixDeg = lambda k, E1=E1: log2(E1(k)) + 8
    sp = run_split(stepP, stepT, seed, KMAX)
    print(f'== {name}: seed 2^{log2(seed)}')
    for k in sorted(sp):
        a, D = sp[k]
        print(f'  k={k:2d}  log2 a/2^k={log2(a)/2**k:7.2f}  log2(2D)/2^k={log2(2*D)/2**k:7.2f}'
              f'  log2 stepP={log2(stepP(k)):6d}  log2 stepT={log2(stepT(k)):6d}  fixDeg={fixDeg(k)}')
    # the class constant: sup over k >= 3 of log2(2 D_k)/2^k, extended by its last value
    vals = {k: log2(2 * sp[k][1]) / 2 ** k for k in sp if k >= 3}
    cmax = max(vals.values())
    cls = lambda k, vals=vals, cmax=cmax: max(vals.get(k, cmax), cmax)
    print(f'  class constant (sup) = {cmax:.2f}')
    print('  envelope: k, class/2^k, mu/2^k, c for 18.1 (d+c), c for 18.2 (L+c)')
    worst1 = worst2 = 0
    for k, cDk, muk, c1, c2 in envelope(cls, fixDeg, 60):
        worst1 = max(worst1, c1); worst2 = max(worst2, c2)
        if k < 10 or k % 10 == 0:
            print(f'    k={k:2d}  {cDk:6.2f}  {muk:8.2f}  d+{c1}  L+{c2}')
    print(f'  worst over k<60: Theorem 18.1 at d+{worst1}, Theorem 18.2 at L+{worst2}')
