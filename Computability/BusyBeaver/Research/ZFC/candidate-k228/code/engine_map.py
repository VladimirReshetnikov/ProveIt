"""Run ProveIt's fold241 table and Elliot Glazer's k230 table from the blank tape in lockstep
for the whole 408,419-step startup, check that they read and write the same tape and move the
same way at every step, and record the induced state map. Every mapped pair must agree on both
rows (same write and move; targets mapped to each other when both are mapped). The result must
equal code/k230_to_fold241.json, which build_k228.py uses.
Usage: engine_map.py FOLD241_old.tm K230.tm"""
import json, os, sys
def load(p):
    T, start = {}, None
    for l in open(p):
        if l.startswith("#! start"): start = int(l.split()[2])
        elif l.strip() and not l.startswith("#"):
            q, b, w, d, z = l.split(); T[int(q), int(b)] = (int(w), d, int(z))
    return T, start
A, qa = load(sys.argv[1]); B, qb = load(sys.argv[2])
ta, tb, ha, hb, m = set(), set(), 0, 0, {}
for step in range(408419):
    assert m.setdefault(qa, qb) == qb, ("state map conflict", step, qa, qb)
    ba, bb = int(ha in ta), int(hb in tb)
    assert ba == bb and (ha == hb), ("tape or head differs", step)
    wa, da, za = A[qa, ba]; wb, db, zb = B[qb, bb]
    assert (wa, da) == (wb, db), ("row differs", step, qa, qb)
    (ta.add if wa else ta.discard)(ha); ha += 1 if da == "R" else -1; qa = za
    (tb.add if wb else tb.discard)(hb); hb += 1 if db == "R" else -1; qb = zb
assert ta == tb and qa == 96 and qb == 84, (qa, qb)
assert len(set(m.values())) == len(m)
for a, b in m.items():
    for x in (0, 1):
        ra, rb = A[a, x], B[b, x]
        assert ra[:2] == rb[:2], ("row disagrees", a, b, x)
        if ra[2] in m: assert m[ra[2]] == rb[2], ("target disagrees", a, b, x)
want = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "k230_to_fold241.json")))["k230_to_fold241"]
got = {str(b): a for a, b in m.items()}
want = {k: v for k, v in want.items() if k != "230"}       # the halt state is not visited
assert got == want, "map differs from k230_to_fold241.json"
print(f"LOCKSTEP_STARTUP_PASS steps 408419; {len(m)} states mapped injectively; both rows of every mapped pair agree; final dispatcher fold241 96 = k230 84; map equals k230_to_fold241.json")
