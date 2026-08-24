"""Exhaustive EXACT integrality search on the toy grid.
Balance weights are [1,5,55,275,3025,15125,75625] for cells
[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]; the (0,0) weight is 1 so
c_{0,0} is determined by the other six.  We enumerate the other six in a box and
test v_p(F) >= 0 for EVERY prime p <= 161051 (exactly, via Legendre)."""
import numpy as np, json, itertools, sys

Vu = np.load("V.npy")            # (379, 7) distinct valuation vectors
lab = json.load(open("lab.json"))
cells = [tuple(x) for x in lab["cells"]]; w = lab["w"]
print("cells",cells,"weights",w)
B = int(sys.argv[1]) if len(sys.argv)>1 else 3

free = list(range(1,7))          # indices of cells other than (0,0)
rng = list(range(-B,B+1))
cands = np.array(list(itertools.product(rng, repeat=6)), dtype=np.int64)
c0 = -(cands @ np.array([w[k] for k in free], dtype=np.int64))
C = np.concatenate([c0[:,None], cands], axis=1)     # full coefficient vectors
nz = np.any(C!=0, axis=1)
C = C[nz]
print("nonzero balanced integer vectors enumerated:", C.shape[0])
# sanity: balance holds exactly
assert np.all(C @ np.array(w, dtype=np.int64) == 0)

def tails_ok(c):
    for j in sorted({j for (i,j) in cells}):
        idx = [k for k,(i,jj) in enumerate(cells) if jj==j]
        idx.sort(key=lambda k: cells[k][0])
        s = 0
        for k in reversed(idx):
            s += c[k]
            if s < 0: return False
    return True

integral = []
CH = 20000
for s in range(0, C.shape[0], CH):
    blk = C[s:s+CH]
    val = blk @ Vu.T                      # (blk, 379) all p-adic valuations of F
    ok = val.min(axis=1) >= 0
    if ok.any():
        for r in np.nonzero(ok)[0]:
            integral.append(blk[r].copy())
print("INTEGRAL nonzero balanced patterns found:", len(integral))
th = 0
for c in integral[:40]:
    t = tails_ok(c)
    th += t
    print("   c =", dict(zip(cells, [int(x) for x in c])), " all-slice-tails>=0:", t)
print("of the listed, top-heavy:", th)
