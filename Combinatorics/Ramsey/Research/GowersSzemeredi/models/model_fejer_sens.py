"""Sensitivity of the L.16 model to the scalings of stepT (Bohr) and the seed."""
import math

src = open('model_fejer.py', encoding='utf8').read().split("KMAX = int")[0]
ns = {}
exec(src, ns)
run_split, envelope, log2 = ns['run_split'], ns['envelope'], ns['log2']

S1 = lambda k: 2 ** (k + 4) * (1 + math.ceil((k + 5) / 2))
E1f = lambda k: 2 ** (3 * k + 7) * S1(k)

P = dict(stepP=lambda k: 2 ** (2 ** (k + 5) + 6), stepT=lambda k: 2 ** (2 ** (k + 6)),
         seed=2 ** 132, fixDeg=lambda k: 2 ** (k + 5) + 7)
F = dict(stepP=lambda k: 64 * E1f(k), stepT=lambda k: E1f(k) ** 2,
         seed=2 ** (log2(E1f(1) ** 2) + 4), fixDeg=lambda k: log2(E1f(k)) + 8)

# s composed across dimensions: printed log2 deg s(k) = 2^(k+6) = 64 + sum_{1<=j<=k} 2^(j+5);
# Fejer analogue: 64 + sum_{1<=j<=k} log2 E1'(j).
sdeg = lambda k: 64 + sum(log2(E1f(j)) + 1 for j in range(1, k + 1))
Fs = dict(F, stepT=lambda k: 2 ** sdeg(k), seed=2 ** (sdeg(1) + 4))

scen = {
    'all printed': P,
    'all fejer (stepT = E1^2)': F,
    'fejer, s composed (stepT = 2^sdeg)': Fs,
    'fejer but printed Bohr stepT': dict(F, stepT=P['stepT']),
    'fejer but printed seed': dict(F, seed=P['seed']),
}
for name, X in scen.items():
    sp = run_split(X['stepP'], X['stepT'], X['seed'], 12)
    vals = {k: log2(2 * sp[k][1]) / 2 ** k for k in sp if k >= 3}
    cmax = max(vals.values())
    cls = lambda k, vals=vals, cmax=cmax: max(vals.get(k, cmax), cmax)
    rows = envelope(cls, X['fixDeg'], 60)
    w1 = max(r[3] for r in rows)
    w2 = max(r[4] for r in rows)
    mx = max(r[2] for r in rows)
    print(f'{name:38s} seed 2^{log2(X["seed"]):4d}  class {cmax:6.2f}  env max {mx:7.1f}  -> d+{w1}  L+{w2}')
print('sdeg(k) for k=1..8:', [sdeg(k) for k in range(1, 9)], ' printed 2^(k+6):', [2 ** (k + 6) for k in range(1, 9)])
