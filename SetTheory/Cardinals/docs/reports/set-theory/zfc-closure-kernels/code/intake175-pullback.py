"""Walk from a found 223-node source back toward the calibrated source.

Interns the found source's leaf paths into exact_reassociate's table, so every
subtree equal to an original one gets its ORIGINAL id; novel = live ids >= N0.
Then anneals with cost K*nodes + novel (cap CAP), starting at the found source,
exporting each <=223-node source that lowers the best novel count.
Usage: pullback.py FOUND.json SEED STEPS T K CAP
"""
import json, math, random, sys, time
import exact_reassociate as X

found, seed, steps, T, K, cap = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                 float(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6]))
rng = random.Random(seed)
N0 = X.N0
leaf_ids = {X.S[i]: i for i in range(len(X.S)) if isinstance(X.S[i][0], str)}
sites = [tuple(x) for x in json.load(open(found))["sites"]]
leaf = {p: (o, a) for p, o, a in sites}


def build(p):
    if p in leaf:
        return leaf_ids[leaf[p]]
    return X.cons(build(p + "0"), build(p + "1"))


root = build("")
novel = lambda r: sum(1 for n in X.live(r) if n >= N0)
sc, nv = X.score(root), novel(root)
assert X.signature(root) == X.signature(X.ROOT), "found source is not equivalent"
print("start", sc, "novel", nv, flush=True)
cost = K * sc[0] + nv
best = nv
hist = []
t0 = time.time()
for s in range(steps):
    n = rng.choice(sorted(X.live(root)))
    rots = X.rotations(n)
    if not rots:
        continue
    alt, d, chunks, allclosed = rng.choice(rots)
    nr = X.replace(root, n, alt)
    sc2 = X.score(nr)
    if sc2[1] > 6 or sc2[0] > cap:
        continue
    nv2 = novel(nr)
    c2 = K * sc2[0] + nv2
    if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
        root, cost, sc, nv = nr, c2, sc2, nv2
        hist.append(dict(node=n, alternative=alt, direction=d, chunks=chunks, all_closed=allclosed))
        if sc[0] <= 223 and nv < best:
            best = nv
            X.export(root, hist, f"pull_{seed}_novel{nv}.json", extra=dict(start_file=found))
            print(f"BEST nodes={sc[0]} novel={nv} depth={sc[2]} step {s}", flush=True)
    if len(X.S) > 300000:
        [(root, hist)] = X.compact([(root, hist)])
        leaf_ids = {X.S[i]: i for i in range(len(X.S)) if isinstance(X.S[i][0], str)}
print(f"DONE best novel {best} final {sc} novel {nv} t={time.time()-t0:.0f}s", flush=True)
