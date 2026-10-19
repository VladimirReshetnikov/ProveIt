"""Apply a plain_folds 'BASE keep delete w0 d0 t0 w1 d1 t1' line to a table.

Deletes state `delete`, redirects every target `delete` to `keep`, and sets the two
rows of `keep`. Usage: build_fold.py TABLE.tm "BASE ..." OUT.tm
"""
import sys
src, line, out = sys.argv[1], sys.argv[2].split(), sys.argv[3]
assert line[0] == "BASE"
keep, dele, w0, d0, t0, w1, d1, t1 = map(int, line[1:])
T = {}
for l in open(src):
    if l.strip() and not l.startswith("#"):
        q, b, w, d, z = l.split(); T[(int(q), int(b))] = (int(w), d, int(z))
N = {k: (w, d, keep if z == dele else z) for k, (w, d, z) in T.items() if k[0] != dele}
N[(keep, 0)] = (w0, "R" if d0 == 1 else "L", t0)
N[(keep, 1)] = (w1, "R" if d1 == 1 else "L", t1)
assert all(z != dele for _, _, z in N.values())
with open(out, "w", newline="\n") as f:
    f.write("#! start 95\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(N.items())))
print(out, "states", len({q for q, _ in N}))
