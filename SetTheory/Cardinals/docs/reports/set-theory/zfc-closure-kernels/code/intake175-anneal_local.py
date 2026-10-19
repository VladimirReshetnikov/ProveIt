"""Locality-penalized reassociation search: a 223-node source with few changed subtrees.

Same exact moves as anneal.py (Source 105's rotations, unchanged library). Cost of a
source = K * distinct_nodes + novel, where novel = live nodes whose id is not an
original id (hash-consing keeps every original subtree at its original id), i.e.
subtrees that differ from the calibrated source. Metropolis acceptance on cost.
Exports every source with <= 223 nodes whose novel count improves on the best so far.
Usage: anneal_local.py SEED RESTARTS STEPS T K CAP
"""
import math, random, sys, time
import exact_reassociate as X

seed, restarts, steps, T, K, cap = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
                                    float(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6]))
rng = random.Random(seed)
N0 = X.N0
best_novel = None
t0 = time.time()


def novel(root):
    return sum(1 for n in X.live(root) if n >= N0)


for r in range(restarts):
    root, hist = X.ROOT, []
    sc = X.score(root); nv = 0
    cost = K * sc[0] + nv
    for s in range(steps):
        nodes = sorted(X.live(root))
        n = rng.choice(nodes)
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
            if sc[0] < 224 and (best_novel is None or nv < best_novel):
                best_novel = nv
                X.export(root, hist, f"local_{seed}_novel{nv}.json")
                print(f"FOUND nodes={sc[0]} novel={nv} depth={sc[2]} restart {r} step {s} moves {len(hist)}", flush=True)
        if len(X.S) > 300000:
            # compaction keeps original ids 0..N0-1 in place (they are always kept and sorted first)
            [(root, hist)] = X.compact([(root, hist)])
    [(root, hist)] = X.compact([(X.ROOT, [])])
print(f"DONE best_novel {best_novel} t={time.time()-t0:.0f}s", flush=True)
