"""Coarsest bisimulation of a Turing table: states are equivalent when, for both read bits, they
write the same bit, move the same way and go to equivalent states (halt targets are their own
class). Merging equivalent states preserves the machine's behaviour on every tape exactly.
Usage: minimize.py TABLE [OUT]"""
import sys

T = {}
start = 0
for l in open(sys.argv[1]):
    if l.startswith("#! start"):
        start = int(l.split()[2])
    elif l.strip() and not l.startswith("#"):
        q, b, w, d, z = l.split(); T[int(q), int(b)] = (int(w), d, int(z))
S = sorted({q for q, _ in T})
cls = {q: 0 for q in S}
def key(q, cls):
    return tuple((T[q, b][0], T[q, b][1], cls.get(T[q, b][2], ("H", T[q, b][2]))) for b in (0, 1))
while True:
    sig = {q: key(q, cls) for q in S}
    ids = {}
    new = {q: ids.setdefault((cls[q], sig[q]), len(ids)) for q in S}
    if len(set(new.values())) == len(set(cls.values())):
        break
    cls = new
groups = {}
for q in S:
    groups.setdefault(cls[q], []).append(q)
merges = [g for g in groups.values() if len(g) > 1]
print(f"{len(S)} states -> {len(groups)} classes; merges: {merges}")
if len(sys.argv) > 2:
    rep = {q: min(g) if start not in g else start for g in groups.values() for q in g}
    N = {(rep[q], b): (w, d, rep.get(z, z)) for (q, b), (w, d, z) in T.items() if rep[q] == q}
    with open(sys.argv[2], "w", newline="\n") as f:
        f.write(f"#! start {start}\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(N.items())))
