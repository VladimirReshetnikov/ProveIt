"""L.16b: the class recursion with the Bohr exponent s that Section 16 actually needs.

Section 16 uses s only through `section16_radius_exponent_budget`
(Proofs16RadiusComparison): s >= 2^83 / (theta_1/4)^11 = 2^105 (2b)^(11 A),
b = 2/(theta gamma), A the theta_1 exponent; this is at most b^(22 A + 105).
The printed s = b^(A^2) (A^2 = 2^(2^(k+6))) is far larger.

Scenarios (all inputs are degrees in the base b, as in model_fejer.py):
  stepP = 64 A           (theta_1 inside the class budget)
  stepT = s-degree       (Bohr exponent)
  seed  = 2^(log2 stepT(1) + 4)   (dimension-two base, Bohr only)
CORRECTION (Notes L.16c): the dimension-two base also carries the piece counts
section16BaseFamilyBound(., polyPieceBudget), whose Lemma 16.3 exponent 10000
puts the Fejer seed near 2^35..2^40, not 2^26. With those seeds the model gives
d+6/L+4, and the d+5/L+3 row printed below for the Bohr-only seed is withdrawn.
  fixDeg = log2 A + 7
"""
import math

src = open('model_fejer.py', encoding='utf8').read().split("KMAX = int")[0]
ns = {}
exec(src, ns)
run_split, envelope, log2 = ns['run_split'], ns['envelope'], ns['log2']

A_printed = lambda k: 2 ** (2 ** (k + 5))
A_fejer = lambda k: 2 ** (3 * k + 7) * 2 ** (k + 4) * (k + 6)   # fejerProductExponent
# log2 A in closed form: the envelope runs to k = 60, where A_printed is not computable
logA_printed = lambda k: 2 ** (k + 5)
logA_fejer = lambda k: (3 * k + 7) + (k + 4) + math.ceil(math.log2(k + 6))


def scenario(A, logA, tight_s):
    stepP = lambda k: 64 * A(k)
    if tight_s:
        stepT = lambda k: 22 * A(k) + 105
    else:
        stepT = lambda k: 2 ** (2 ** (k + 6))
    seed = 2 ** (log2(stepT(1)) + 4)
    fixDeg = lambda k: logA(k) + 7
    return stepP, stepT, seed, fixDeg


for name, A, logA, tight in (
        ('printed theta_1, printed s', A_printed, logA_printed, False),
        ('printed theta_1, tight s', A_printed, logA_printed, True),
        ('Fejer theta_1, tight s', A_fejer, logA_fejer, True)):
    stepP, stepT, seed, fixDeg = scenario(A, logA, tight)
    sp = run_split(stepP, stepT, seed, 12)
    vals = {k: log2(2 * sp[k][1]) / 2 ** k for k in sp if k >= 3}
    cmax = max(vals.values())
    cls = lambda k, vals=vals, cmax=cmax: max(vals.get(k, cmax), cmax)
    rows = envelope(cls, fixDeg, 60)
    w1 = max(r[3] for r in rows)
    w2 = max(r[4] for r in rows)
    mx = max(r[2] for r in rows)
    print(f'{name:30s} seed 2^{log2(seed):4d}  class {cmax:6.2f}  env max {mx:7.1f}  -> d+{w1}  L+{w2}')
