"""Build the 228-state table from Elliot Glazer's k230 (github.com/elliotglazer/k230-rocq @ 3142e4d).

k230 keeps ProveIt's fold241 engine and blank initialization unchanged: run from blank, the two
machines agree step for step for all 408,419 startup transitions, and the induced map of 133
states extends without conflict to 50 of the 51 engine states. This script

  1. renumbers k230 into fold241's inherited labels (start 95, dispatcher 96, halt 254) through
     that map, so that every ProveIt checker with hard-coded engine labels applies unchanged;
  2. applies ProveIt's delayed erasure (Sources 101/102; the 239 -> 238 step): delete 169,
     147/0 -> 0R80, 80/0 -> 0L106, 91/1 -> 1L167                            (229 states);
  3. applies the Rotation240 source rotation (commit e5c2b3337e): every subtree
     ((CD6 (CI5 CC2)) CI5) becomes (CI5 (CD6 CC2)) (four occurrences, 5,125 -> 5,121 leaves),
     with 142/0 -> 0R72, 142/1 -> 1R17; then fold 90 into 72: delete 90, 79/1 -> 1R72,
     72/0 -> 0L144, 72/1 -> 1L36                                            (228 states);
  4. writes the inherited-label and canonical (start 0, others ascending, halt 228) tables.

Every edited row is first asserted to hold exactly the value it held in ProveIt's table.
Usage: build_k228.py K230.tm SITES230.json OUTDIR
"""
import hashlib, json, os, sys

k230_tm, k230_sites, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)

# fold241 label -> k230 label for the 133 states visited by the common blank startup
# (equal transition rows under this map; see align.py / engmap.py)
MAP = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "k230_to_fold241.json")))
inv = {int(k): v for k, v in MAP["k230_to_fold241"].items()}

def load(path):
    T, start = {}, None
    for line in open(path):
        if line.startswith("#! start"):
            start = int(line.split()[2])
        elif line.strip() and not line.startswith("#"):
            q, b, w, d, z = line.split(); T[int(q), int(b)] = (int(w), d, int(z))
    return T, start

def text(T, start):
    return f"#! start {start}\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(T.items()))

def write(name, s):
    with open(os.path.join(out, name), "w", newline="\n") as f:
        f.write(s)
    return hashlib.sha256(s.encode()).hexdigest()

K, start = load(k230_tm)
assert start == 0 and len(K) == 460
states = sorted({q for q, _ in K})
halt = 230
assert {z for *_, z in K.values()} - set(states) == {halt}
used = {inv[q] for q in states if q in inv}
free = [x for x in range(254) if x not in used]
ren = {q: (inv[q] if q in inv else free.pop(0)) for q in states}
ren[halt] = 254
assert ren[0] == 95 and ren[84] == 96 and len(set(ren.values())) == len(ren)
T = {(ren[q], b): (w, d, ren[z]) for (q, b), (w, d, z) in K.items()}
rec = {"k230_sha256": hashlib.sha256(open(k230_tm, "rb").read()).hexdigest(),
       "k230_relabel": {str(k): v for k, v in ren.items()}}
rec["k230_inherited_sha256"] = write("k230_inherited_old.tm", text(T, 95))

def edit(T, q, b, old, new):
    assert T[q, b] == old, (q, b, T[q, b], old)
    T[q, b] = new

def delete(T, q):
    del T[q, 0], T[q, 1]
    assert all(z != q for *_, z in T.values())

# 2. delayed erasure
D = dict(T)
edit(D, 147, 0, (0, "R", 169), (0, "R", 80))
edit(D, 80, 0, (0, "R", 25), (0, "L", 106))
edit(D, 91, 1, (0, "L", 50), (1, "L", 167))
delete(D, 169)
rec["delayed229_sha256"] = write("delayed229_old.tm", text(D, 95))

# 3. source rotation and 90/72 fold
raw = json.load(open(k230_sites))
code = {"EInc": "CI", "EDecnz": "CD", "EBreak": "CB", "EContinue": "CC", "EHalt": "CH"}
sites = []
for p, k in raw:
    t = k.split(); sites.append([p, code[t[0]], int(t[1]) if len(t) > 1 else None])
leaf = {p: (o, a) for p, o, a in sites}
def sub(p):
    return leaf[p] if p in leaf else (sub(p + "0"), sub(p + "1"))
OLD = ((("CD", 6), (("CI", 5), ("CC", 2))), ("CI", 5))
prefixes = sorted({p[:i] for p in leaf for i in range(len(p))})
occ = [p for p in prefixes if sub(p) == OLD]
assert len(occ) == 4, occ
new = [s for s in sites if not any(s[0].startswith(o) for o in occ)]
for o in occ:
    new += [[o + "0", "CI", 5], [o + "10", "CD", 6], [o + "11", "CC", 2]]
new.sort(key=lambda s: s[0])
assert len(new) == len(sites) - 4
rec["rotated_occurrences"] = occ
rec["k230_sites_logical_sha256"] = write("k230_sites_logical.json", json.dumps(sites, indent=0) + "\n")
rec["k228_sites_logical_sha256"] = write("sites_logical.json", json.dumps(new, indent=0) + "\n")
F = dict(D)
edit(F, 142, 0, (0, "R", 37), (0, "R", 72))
edit(F, 142, 1, (1, "R", 72), (1, "R", 17))
edit(F, 79, 1, (1, "R", 90), (1, "R", 72))
edit(F, 72, 0, (0, "R", 57), (0, "L", 144))
edit(F, 72, 1, (0, "R", 64), (1, "L", 36))
delete(F, 90)
assert len({q for q, _ in F}) == 228
rec["k228_inherited_sha256"] = write("zfc_k228_old.tm", text(F, 95))

# 4. canonical numbering: start 0, other working states ascending, halt 228
work = sorted({q for q, _ in F})
order = [95] + [q for q in work if q != 95]
can = {q: i for i, q in enumerate(order)}; can[254] = len(order)
C = {(can[q], b): (w, d, can[z]) for (q, b), (w, d, z) in F.items()}
rec["k228_canonical_sha256"] = write("zfc_k228.tm", text(C, 0))
rec["renumbering_old_to_new"] = {str(k): v for k, v in can.items()}
write("build_record.json", json.dumps(rec, indent=1) + "\n")
print(json.dumps({k: v for k, v in rec.items() if k.endswith("sha256")}, indent=1))
