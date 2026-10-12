exec(open('model_fejer_sens.py', encoding='utf8').read().split("scen = {")[0])
for s in range(80, 133, 4):
    X = dict(Fs, seed=2 ** s)
    sp = run_split(X['stepP'], X['stepT'], X['seed'], 12)
    vals = {k: log2(2 * sp[k][1]) / 2 ** k for k in sp if k >= 3}
    cmax = max(vals.values())
    cls = lambda k, vals=vals, cmax=cmax: max(vals.get(k, cmax), cmax)
    rows = envelope(cls, X['fixDeg'], 60)
    print(s, round(cmax, 2), 'd+%d L+%d' % (max(r[3] for r in rows), max(r[4] for r in rows)))
