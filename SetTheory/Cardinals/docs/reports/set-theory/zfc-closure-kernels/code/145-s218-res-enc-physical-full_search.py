"""Rotation-chain search for simulation folds (the 221's mechanism).

Explores closed node-neutral source rotations (rot_lib, the in-process rotgen) from a start
table: level 1 and 2 in full, level 3 only through rotations sharing a decoder state with the
previous one. On every table it runs a fast simulation-fold detector: pairs (K, D) with a known,
different bit in the radius-R invariant and one read bit already acting identically after
D -> K; the other read bit is accepted only through a bounded symbolic simulation (sim_fold.run)
in both contexts. Writes each hit (table + sites + chain) and prints a summary.
Usage: rot_fold_search.py TABLE SITES OUTDIR [DEPTH] [MAXZR] [RADIUS] [MAXSTEPS]"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inv_fold import load, invariant
from sim_fold import run
import rot_full as rot_lib

def fast_folds(T, st, R, ms):
    inv = invariant(T, st, R)
    S = sorted({q for q, _ in T})
    hits = []
    for K in S:
        if K not in inv: continue
        for D in S:
            if D == K or D not in inv: continue
            if not any(o in inv[D] and inv[D][o] != v for o, v in inv[K].items()): continue
            red = lambda z: K if z == D else z
            same = [r for r in (0, 1) if T[K, r][:2] == T[D, r][:2] and red(T[K, r][2]) == red(T[D, r][2])]
            if not same: continue
            if len(same) == 2:
                hits.append((K, D, {0: "same", 1: "same"})); continue
            r = 1 - same[0]
            M = {k: (w, d, red(z)) for k, (w, d, z) in T.items() if k[0] != D}
            goals = {}
            for X in (K, D):
                if 0 in inv[X] and inv[X][0] != r: continue
                w, d, z = T[X, r]
                tape = dict(inv[X]); tape[0] = r
                after = dict(tape); after[0] = w
                goals[X] = (tape, (red(z), 1 if d == "R" else -1, after))
            if not goals:
                hits.append((K, D, {same[0]: "same", r: "unreachable"})); continue
            for m in ("L", "R"):
                found = None
                for h in S:
                    if h == D: continue
                    M2 = dict(M); M2[K, r] = (r, m, h)
                    if all(run(M2, K, tape, 0, ms, goal) is not None for tape, goal in goals.values()):
                        found = (r, m, h); break
                if found:
                    hits.append((K, D, {same[0]: "same", r: found})); break
    return hits

def main():
    tab, sites, out = sys.argv[1], sys.argv[2], sys.argv[3]
    depth = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    maxzr = int(sys.argv[5]) if len(sys.argv) > 5 else 7
    R = int(sys.argv[6]) if len(sys.argv) > 6 else 8
    ms = int(sys.argv[7]) if len(sys.argv) > 7 else 7
    os.makedirs(out, exist_ok=True)
    T0, st = load(tab); S0 = [list(x) for x in json.load(open(sites))]
    t0 = time.time(); seen = 0; nhits = 0
    def zr(sites):
        return max(len(p) - len(p.rstrip("0")) for p, *_ in sites)
    def visit(T, S, chain, last_states, z=None):
        nonlocal seen, nhits
        seen += 1
        pairs={}
        for aq in sorted({q for q,c in T}):
            sig=(T[aq,0],T[aq,1])
            if sig in pairs:
                dq=aq;kq=pairs[sig]
                tag=f"duplicate{seen:05d}_{kq}_{dq}"
                json.dump({"chain":chain,"keep":kq,"delete":dq},open(os.path.join(out,tag+".json"),"w"))
                json.dump(S,open(os.path.join(out,tag+"_sites.json"),"w"))
                N={key:(w,d,kq if z==dq else z)for key,(w,d,z)in T.items()if key[0]!=dq}
                with open(os.path.join(out,tag+".tm"),"w")as f:
                    f.write(f"#! start {st}\n"+"".join(f"{q} {b} {w} {d} {z}\n"for(q,b),(w,d,z)in sorted(N.items())))
                print("DUPLICATE",tag,chain,len(N)//2,flush=True)
            pairs[sig]=aq
        if len(T)<len(T0):
            tag=f"direct{seen:05d}"
            json.dump({"chain":chain},open(os.path.join(out,tag+".json"),"w"))
            json.dump(S,open(os.path.join(out,tag+"_sites.json"),"w"))
            with open(os.path.join(out,tag+".tm"),"w")as f:
                f.write(f"#! start {st}\n"+"".join(f"{q} {b} {w} {d} {z}\n"for(q,b),(w,d,z)in sorted(T.items())))
            print("DIRECT",tag,chain,len(T)//2,flush=True)
        if chain and (z if z is not None else zr(S)) <= 6:
            for K, D, plan in fast_folds(T, st, R, ms):
                nhits += 1
                tag = f"hit{nhits:03d}"
                json.dump({"chain": chain, "keep": K, "delete": D, "plan": {str(k): v for k, v in plan.items()}},
                          open(os.path.join(out, tag + ".json"), "w"))
                with open(os.path.join(out, tag + ".tm"), "w", newline="\n") as f:
                    f.write(f"#! start {st}\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(T.items())))
                json.dump(S, open(os.path.join(out, tag + "_sites.json"), "w"))
                print("HIT", tag, chain, "keep", K, "delete", D, plan, flush=True)
        if len(chain) >= depth:
            return
        for tagr, N, S2, z2 in rot_lib.rotations(T, S, maxzr):
            states = set(int(x) for x in tagr.split("_")[1:3])
            if len(chain) >= 2 and not (states & last_states):
                continue
            visit(N, S2, chain + [tagr], states, z2)
            if len(chain) == 0:
                print(f"  level-1 {tagr} done; tables {seen}, hits {nhits}, t={time.time()-t0:.0f}s", flush=True)
    visit(T0, S0, [], set())
    print(f"DONE tables {seen} hits {nhits} t={time.time()-t0:.0f}s", flush=True)

main()
