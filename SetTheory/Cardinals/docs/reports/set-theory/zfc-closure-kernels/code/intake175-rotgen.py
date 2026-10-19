"""Enumerate node-neutral source rotations that compile by repurposing one decoder state.

Input: an inherited-label table and its sites file. For every interior node X:
  L: X=(A,Y), Y=(B,C)  ->  X=(Z,C), Z=(A,B)      (Z gets Y's decoder state)
  R: X=(Y,C), Y=(A,B)  ->  X=(A,Z), Z=(B,C)
Admissible iff (Source 105 criterion) the first chunk has no escaping break and the
last chunk no escaping continue; Y must have X as its ONLY parent (so Y disappears),
Z must not already exist (node count stays the same), states of X and Y must be
unique and unshared on plain decoder paths, and the rotated source must keep zero
run <= 6. Rows (write := read bit for every moved row):
  L: X/0 = (0,R,q_Y)      X/1 = old Y/1     Z/0 = old X/0   Z/1 = old Y/0
  R: X/0 = old Y/0        X/1 = (1,R,q_Y)   Z/0 = old Y/1   Z/1 = old X/1
Writes each candidate as <out>/<tag>.tm and <tag>.sites.json plus index.json.
Usage: rotgen.py TABLE SITES OUTDIR
"""
import json, os, sys
from collections import defaultdict
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "s236"))
from dag import DAG, load_sites

table_path, sites_path, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
T, header = {}, "#! start 95\n"
for line in open(table_path):
    if line.strip() and not line.startswith("#"):
        q, b, w, d, z = line.split(); T[(int(q), int(b))] = (int(w), d, int(z))
d = DAG(load_sites(sites_path))
S = d.struct
inter = lambda n: not isinstance(S[n][0], str)

# decoder map on plain paths
qnodes = defaultdict(set)
for p in sorted({p[:i] for p in d.leaf for i in range(len(p))}):
    q = 96
    for b in p:
        w, mv, z = T[(q, int(b))]
        if w != int(b) or mv != "R":
            break
        q = z
    else:
        qnodes[q].add(d.pathnode[p])
node_states = defaultdict(set)
for q, ns in qnodes.items():
    for n in ns:
        node_states[n].add(q)
def state_of(n):
    qs = node_states.get(n, set())
    if len(qs) != 1:
        return None
    q = next(iter(qs))
    return q if qnodes[q] == {n} else None

parents = defaultdict(set)
for n in d.interior():
    for c in S[n]:
        parents[c].add(n)

def boundary(n, memo={}):
    if n in memo: return memo[n]
    x = S[n]
    if not inter(n):
        o, a = x
        r = (1, 0, False) if o == "CD" else (a, 0, False) if o == "CB" else (0, a, False) if o == "CC" else (0, 0, o == "CH")
    else:
        u, v = boundary(x[0]), boundary(x[1])
        r = (max(max(u[0] - 1, 0), v[0]), max(u[1], max(v[1] - 1, 0)), u[2] or v[2])
    memo[n] = r
    return r

def rebuild(X, newX):
    """sites of the source in which every occurrence of node X is replaced by tuple tree newX."""
    sites = []
    def emit(n, p):
        if n == X:
            emit_tree(newX, p); return
        x = S[n]
        if not inter(n):
            sites.append([p, x[0], x[1]]); return
        emit(x[0], p + "0"); emit(x[1], p + "1")
    def emit_tree(t, p):
        if isinstance(t, int):
            emit(t, p); return
        emit_tree(t[0], p + "0"); emit_tree(t[1], p + "1")
    emit(d.root, "")
    return sorted(sites)

existing = set(S)
cands = []
for X in d.interior():
    qX = state_of(X)
    if qX is None:
        continue
    a, b = S[X]
    for kind in ("L", "R"):
        Y = b if kind == "L" else a
        if not inter(Y) or parents[Y] != {X}:
            continue
        qY = state_of(Y)
        if qY is None or qY == qX:
            continue
        if kind == "L":
            A, (B, C) = a, S[Y]
        else:
            (A, B), C = S[Y], b
        if boundary(A)[0] != 0 or boundary(C)[1] != 0:
            continue
        Z = (A, B) if kind == "L" else (B, C)
        if Z in existing:
            continue                      # would merge nodes: handled separately
        rows = [T[(qX, 0)], T[(qX, 1)], T[(qY, 0)], T[(qY, 1)]]
        N = dict(T)
        if kind == "L":
            N[(qX, 0)] = (0, "R", qY); N[(qX, 1)] = (1,) + T[(qY, 1)][1:]
            N[(qY, 0)] = (0,) + T[(qX, 0)][1:]; N[(qY, 1)] = (1,) + T[(qY, 0)][1:]
            newX = ((A, B), C)
        else:
            N[(qX, 0)] = (0,) + T[(qY, 0)][1:]; N[(qX, 1)] = (1, "R", qY)
            N[(qY, 0)] = (0,) + T[(qY, 1)][1:]; N[(qY, 1)] = (1,) + T[(qX, 1)][1:]
            newX = (A, (B, C))
        sites = rebuild(X, newX)
        zr = max(max(map(len, p.split("1"))) for p, _, _ in sites)
        depth = max(len(p) for p, _, _ in sites)
        if zr > 6:
            continue
        tag = f"{kind}_{qX}_{qY}"
        with open(os.path.join(out, tag + ".tm"), "w", newline="\n") as f:
            f.write(header + "".join(f"{q} {bb} {w} {mv} {z}\n" for (q, bb), (w, mv, z) in sorted(N.items())))
        json.dump(sites, open(os.path.join(out, tag + ".sites.json"), "w"), indent=0)
        with open(os.path.join(out, tag + ".sites.txt"), "w", newline="\n") as f:
            f.write("".join(f"{p} {o} {0 if a_ is None else a_}\n" for p, o, a_ in sites))
        cands.append(dict(tag=tag, X=X, Y=Y, qX=qX, qY=qY, kind=kind, depth=depth, zero_run=zr,
                          plain=all(r[0] == i % 2 for i, r in enumerate(rows))))
json.dump(cands, open(os.path.join(out, "index.json"), "w"), indent=1)
print(len(cands), "candidates;", sum(c["plain"] for c in cands), "with all four rows plain")
