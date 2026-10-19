"""Randomized reassociation search for a source with fewer distinct subtrees.

Uses Source 105's exact_reassociate.py UNCHANGED as a library: its rotations()
admit exactly the broader-criterion reassociations (A without escaping break,
C without escaping continue), each preserving the node's exact local control
signature; replace() rebuilds the DAG. Unlike its capped beam, this walk may
temporarily ADD nodes: a move from n nodes to n' is accepted when
n' <= n, or with probability exp(-(n'-n)/T) otherwise, never above CAP.
The zero-run limit 6 is kept throughout. Any state with < 224 nodes is exported.
Usage: anneal.py SEED RESTARTS STEPS T CAP
"""
import math, random, sys, json, time
import exact_reassociate as X

seed, restarts, steps, T, cap = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
                                 float(sys.argv[4]), int(sys.argv[5]))
rng = random.Random(seed)
best_overall = None
t0 = time.time()
for r in range(restarts):
    root, hist = X.ROOT, []
    cur = X.score(root)
    best = cur
    for s in range(steps):
        nodes = sorted(X.live(root))
        n = rng.choice(nodes)
        rots = X.rotations(n)
        if not rots:
            continue
        alt, d, chunks, allclosed = rng.choice(rots)
        nr = X.replace(root, n, alt)
        sc = X.score(nr)
        if sc[1] > 6 or sc[0] > cap:
            continue
        delta = sc[0] - cur[0]
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            root, cur = nr, sc
            hist.append(dict(node=n, alternative=alt, direction=d, chunks=chunks, all_closed=allclosed))
            if sc[0] < best[0]:
                best = sc
            if sc[0] < 224:
                X.export(root, hist, f"anneal_found_{seed}_{r}.json")
                print("FOUND", sc, "restart", r, "step", s, flush=True)
                sys.exit(0)
        if len(X.S) > 400000:          # keep the hash-cons table bounded
            [(root, hist)] = X.compact([(root, hist)])
    print(f"restart {r}: final {cur} best {best} moves {len(hist)} t={time.time()-t0:.0f}s", flush=True)
    best_overall = best if best_overall is None or best < best_overall else best_overall
    [(root, hist)] = X.compact([(X.ROOT, [])])
print("DONE best", best_overall)
