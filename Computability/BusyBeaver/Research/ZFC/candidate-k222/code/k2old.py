"""Relabel a K-labelled K-family table (start 0, dispatcher 84, halt 254) into fold241's inherited
labels (start 95, dispatcher 96, halt 254) for Source 103's checkers. Inherited K labels go
through the K230 -> old map; any other label (fresh compile labels) gets the lowest free label
below 254. Usage: k2old.py LEGACY_MAP K_TABLE OUT"""
import json, sys

m = {int(k): v for k, v in json.load(open(sys.argv[1]))["k230_to_old"].items()}
T = {}
for l in open(sys.argv[2]):
    if l.strip() and not l.startswith("#"):
        q, b, w, d, z = l.split(); T[int(q), int(b)] = (int(w), d, int(z))
states = sorted({q for q, _ in T})
ren = {254: 254}
for q in states:
    if q in m and q != 230:
        ren[q] = m[q]
used = set(ren.values())
free = [x for x in range(254) if x not in used]
for q in states:
    if q not in ren:
        ren[q] = free.pop(0)
assert ren[0] == 95 and ren[84] == 96, (ren[0], ren[84])
assert len(set(ren[q] for q in states)) == len(states)
N = {(ren[q], b): (w, d, ren[z]) for (q, b), (w, d, z) in T.items()}
with open(sys.argv[3], "w", newline="\n") as f:
    f.write("#! start 95\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(N.items())))
print("relabelled", len(states), "states; fresh labels", sorted(q for q in states if q not in m or q == 230))
