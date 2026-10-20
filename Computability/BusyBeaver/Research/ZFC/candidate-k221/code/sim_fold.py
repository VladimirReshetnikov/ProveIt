"""Simulation-based fold scan (generalizes inv_fold.py; calibrated on the 221's own fold).

For keep K and delete D (any pair with a known, different bit in the radius-R invariant), the
merged machine redirects D -> K. For each read bit r: if K/r and D/r agree after the redirect,
keep it; otherwise try a new row K/r := (r, m, h) for every move m and existing state h. Accept
it if, from the invariant-known tape of K (resp. D) with r under the head, the merged machine
reaches, within MAXSTEPS steps and reading only known cells, exactly the configuration one old
step of K (resp. D) produces: the old target state (with D -> K), the old head move, and the
old tape with cell 0 := old write. The invariant is recomputed on the folded table and its
soundness for the new rows is checked by the same dataflow; every candidate still needs the
end-to-end screen and unbounded runtime.
Usage: sim_fold.py TABLE [RADIUS] [MAXSTEPS] [OUTDIR]"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inv_fold import load, invariant

def run(T, q, tape, head, steps, goal):
    """run merged table T from (q, head) on partial tape; True iff it reaches goal exactly"""
    tape = dict(tape)
    for n in range(steps + 1):
        if (q, head, tape) == goal:
            return n
        if n == steps or head not in tape or (q, tape[head]) not in T:
            return None
        w, d, z = T[q, tape[head]]
        tape[head] = w; head += 1 if d == "R" else -1; q = z
    return None

def scan(T, inv, maxsteps, R):
    S = sorted({q for q, _ in T})
    out = []
    for K in S:
        for D in S:
            if K == D or K not in inv or D not in inv:
                continue
            if not any(o in inv[D] and inv[D][o] != v for o, v in inv[K].items()):
                continue
            M = {k: (w, d, K if z == D else z) for k, (w, d, z) in T.items() if k[0] != D}
            red = lambda z: K if z == D else z
            plan = {}
            for r in (0, 1):
                if 0 in inv[K] and inv[K][0] != r and 0 in inv[D] and inv[D][0] != r:
                    plan[r] = "unreachable"; continue
                if T[K, r][:2] == T[D, r][:2] and red(T[K, r][2]) == red(T[D, r][2]):
                    plan[r] = "same"; continue
                if 0 in inv[D] and inv[D][0] != r:          # D never reads r: K keeps its row
                    plan[r] = "keepK"; continue
                if 0 in inv[K] and inv[K][0] != r:          # K never reads r: its row is free
                    w, d, z = T[D, r]; plan[r] = (w, d, red(z)); continue
                goals = {}
                for X in (K, D):
                    if 0 in inv[X] and inv[X][0] != r:
                        continue                                 # X never reads r
                    w, d, z = T[X, r]
                    tape = dict(inv[X]); tape[0] = r
                    after = dict(tape); after[0] = w
                    goals[X] = (tape, (red(z), 1 if d == "R" else -1, after))
                found = None
                for m in ("L", "R"):
                    for h in S:
                        if h == D: continue
                        ok = True
                        for X, (tape, goal) in goals.items():
                            t2 = dict(tape); t2[0] = r
                            M2 = dict(M); M2[K, r] = (r, m, h)
                            if run(M2, K, t2, 0, maxsteps, goal) is None:
                                ok = False; break
                        if ok:
                            found = (r, m, h); break
                    if found: break
                if found is None:
                    break
                plan[r] = found
            if len(plan) == 2:
                out.append((K, D, plan))
    return out

def apply(T, K, D, plan):
    N = {k: (w, d, K if z == D else z) for k, (w, d, z) in T.items() if k[0] != D}
    for r, p in plan.items():
        if isinstance(p, tuple):
            N[K, r] = p

    return N

if __name__ == "__main__":
    T, st = load(sys.argv[1])
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    ms = int(sys.argv[3]) if len(sys.argv) > 3 else 7
    inv = invariant(T, st, R)
    c = scan(T, inv, ms, R)
    print(f"{len({q for q, _ in T})} states; {len(c)} fold candidates")
    for K, D, plan in c[:40]:
        print("  keep", K, "delete", D, plan)
    if len(sys.argv) > 4:
        os.makedirs(sys.argv[4], exist_ok=True)
        for K, D, plan in c:
            N = apply(T, K, D, plan)
            with open(os.path.join(sys.argv[4], f"fold_{K}_{D}.tm"), "w", newline="\n") as f:
                f.write(f"#! start {st}\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(N.items())))
