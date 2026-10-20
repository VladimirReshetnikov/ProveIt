"""Invariant-based left-bit fold scan of a Turing table.

1. Inductive tape invariant: for each state, the bits known at offsets -R..R from the head on
   every arrival, by a greatest-fixpoint dataflow over all transitions from an unconstrained start
   state (a state's knowledge is the intersection over its incoming transitions).
2. Fold candidates (keep K, delete D): K and D have known, different bits tK != tD at offset -1.
   For each read bit r either K/r == D/r, or a helper h with h/0 = (0,R,u0), h/1 = (1,R,u1),
   u_tK/r == K/r and u_tD/r == D/r (u_* not K or D); then K/r := (r, L, h). D's callers are
   redirected to K. Every candidate must still be checked end to end (screen, runtime).
Usage: inv_fold.py TABLE [RADIUS] [OUTDIR]"""
import sys, os

def load(p):
    T, st = {}, None
    for l in open(p):
        if l.startswith("#! start"): st = int(l.split()[2])
        elif l.strip() and not l.startswith("#"):
            q, b, w, d, z = l.split(); T[int(q), int(b)] = (int(w), d, int(z))
    return T, st

def invariant(T, start, R):
    S = {q for q, _ in T}
    inv = {start: {}}
    work = [start]
    while work:
        q = work.pop()
        for b in (0, 1):
            k = inv[q]
            if 0 in k and k[0] != b:
                continue                          # this read is impossible here
            w, d, z = T[q, b]
            if z not in S:
                continue
            post = dict(k); post[0] = w
            sh = 1 if d == "R" else -1
            post = {o - sh: v for o, v in post.items() if -R <= o - sh <= R}
            if z not in inv:
                inv[z] = post; work.append(z)
            else:
                new = {o: v for o, v in inv[z].items() if post.get(o) == v}
                if new != inv[z]:
                    inv[z] = new; work.append(z)
    return inv

def folds(T, inv):
    S = sorted({q for q, _ in T})
    out = []
    tag = {q: inv[q].get(-1) for q in S if q in inv}
    for K in S:
        for D in S:
            if K == D or tag.get(K) is None or tag.get(D) is None or tag[K] == tag[D]:
                continue
            plan = {}
            for r in (0, 1):
                if T[K, r] == T[D, r]:
                    plan[r] = "same"; continue
                found = None
                for h in S:
                    if h in (K, D): continue
                    (w0, d0, u0), (w1, d1, u1) = T[h, 0], T[h, 1]
                    if (w0, d0, w1, d1) != (0, "R", 1, "R") or {u0, u1} & {K, D}: continue
                    u = {0: u0, 1: u1}
                    if (u[tag[K]], r) in T and (u[tag[D]], r) in T and \
                       T[u[tag[K]], r] == T[K, r] and T[u[tag[D]], r] == T[D, r]:
                        found = h; break
                if found is None: break
                plan[r] = found
            if len(plan) == 2:
                out.append((K, D, plan))
    return out

def apply(T, K, D, plan):
    N = {}
    for (q, b), (w, d, z) in T.items():
        if q == D: continue
        N[q, b] = (w, d, K if z == D else z)
    for r, h in plan.items():
        if h != "same":
            N[K, r] = (r, "L", h)
    return N

if __name__ == "__main__":
    T, st = load(sys.argv[1]); R = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    inv = invariant(T, st, R)
    tagged = sum(1 for q in inv if -1 in inv[q])
    c = folds(T, inv)
    print(f"{len({q for q, _ in T})} states, {len(inv)} reached, {tagged} with a known left bit; {len(c)} fold candidates")
    for K, D, plan in c[:30]:
        print("  keep", K, "delete", D, plan)
    if len(sys.argv) > 3:
        os.makedirs(sys.argv[3], exist_ok=True)
        for i, (K, D, plan) in enumerate(c):
            N = apply(T, K, D, plan)
            with open(os.path.join(sys.argv[3], f"fold_{K}_{D}.tm"), "w", newline="\n") as f:
                f.write(f"#! start {st}\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(N.items())))
