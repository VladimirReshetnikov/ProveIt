"""Run two source programs as register machines (semantics of Source 103's independent_runtime:
inc / strip) from the post-startup registers, and compare the sequences of (pc, registers) at
every executed leaf outside the rewritten subtrees. Usage: rmcompare.py A_SITES B_SITES STEPS PREFIX..."""
import json, sys, importlib.util
import os
spec = importlib.util.spec_from_file_location("ir", os.path.join(os.path.dirname(os.path.abspath(__file__)), "independent_runtime.py"))
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
A, B = (json.load(open(x)) for x in sys.argv[1:3]); N = int(sys.argv[3]); occ = sys.argv[4:]
PHY = r.PHY; phys = [0, 0, 0, 3, 0, 0, 3, 0, 0]
regs0 = [phys[PHY[i]] for i in range(9)]
def mk(sites):
    leaf = {p: (o, a) for p, o, a in sites}; pre = {p[:i] for p in leaf for i in range(len(p))}
    def find(P):
        p = ""
        i = 0
        while p not in leaf:
            p += P[i] if i < len(P) else "0"; i += 1
            assert p in leaf or p in pre, p
        return p
    return leaf, find
def run(sites):
    leaf, find = mk(sites); P = ""; regs = list(regs0)
    for t in range(N):
        p = find(P); o, a = leaf[p]
        if not any(p.startswith(x) for x in occ):
            yield (p, tuple(regs))
        if o == "CH": yield ("HALT",); return
        if o == "CI": regs[a] += 1; P, _ = r.inc(p)
        elif o == "CD" and regs[a] > 0: regs[a] -= 1; P, _ = r.inc(p)
        elif o in ("CD", "CB"): P, _ = r.inc(r.strip(p, "0", a if o == "CB" else 1))
        elif o == "CC": P = r.strip(p, "1", a)
ga, gb = run(A), run(B); n = 0
for x in ga:
    y = next(gb, None)
    if x != y:
        print("DIFFER at outside event", n, x[:1], y[:1] if y else None); sys.exit(1)
    n += 1
print("IDENTICAL outside-event sequences:", n, "events within", N, "steps of A")
