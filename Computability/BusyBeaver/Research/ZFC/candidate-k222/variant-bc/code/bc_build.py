"""Build B+C sources: Source 129's seed-root source with the helper removed from its bundle
(B's idea) and B's G row. Variants differ in which final 119 unit is dropped and in how the
pattern collapses. Writes each variant and prints metrics.
Usage: bc_build.py OUTDIR"""
import json, sys, itertools
from functools import cache
from pathlib import Path

S = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad")
sys.path.insert(0, str(S / "intake179/fresh/K225_Construction_2026-10-19/K225_Construction_2026-10-19/portable/baseline226/verification"))
sys.path.insert(0, str(S / "intake181/fresh/K224_Construction_2026-10-20/K224_Construction_2026-10-20/portable/verification"))
import reconstruct227 as c
import construct_rel225 as cr

CP = S / "intake186/fresh/c/K223_Construction_2026-10-20/portable/machine"
g = json.load(open(CP / "grammar223.json"))
src = c.tree(json.loads((CP / "sites.json").read_text()))
AP = g["ancestor_path"]
region = c.subtree(src, AP)

# unit subtrees, by walking the pattern against the actual region
unit = {}
def walk(p, t):
    if isinstance(p, int):
        unit[p] = t; return
    assert not c.leaf(t)
    walk(p[0], t[0]); walk(p[1], t[1])
walk(g["pattern"], region)
assert sorted(unit) == list(range(len(g["units"])))
for i, u in enumerate(g["units"]):
    assert len(c.sites(unit[i])) == u["leaves"], i
roles = g["units"]
h_units = {i for i, u in enumerate(roles) if isinstance(u["role"], dict) and 9 <= u["role"]["word_index"] <= 19}
r119 = [i for i, u in enumerate(roles) if isinstance(u["role"], dict) and u["role"]["word_index"] in (74, 75)]
print("H units", min(h_units), "..", max(h_units), len(h_units), "| final 119 units", r119)

def drop(p, gone):
    if isinstance(p, int):
        return None if p in gone else p
    a, b = drop(p[0], gone), drop(p[1], gone)
    if a is None: return b
    if b is None: return a
    return [a, b]
def assemble(p):
    return unit[p] if isinstance(p, int) else (assemble(p[0]), assemble(p[1]))

# B's G row and rotation (construct_g226.py), macros from parent225's decoder
P225 = S / "intake181/fresh/K224_Construction_2026-10-20/K224_Construction_2026-10-20/portable/parent225"
groups, _ = cr.decoder_map(c, cr.read_table(P225 / "candidate225.k.tm"), c.tree(json.loads((P225 / "sites225.json").read_text())))
q = lambda k: cr.sole(groups, k)
rel, eq, all_, pair_inc = q(155), q(182), q(86), q(99)
@cache
def size(n): return 1 if c.leaf(n) else size(n[0]) + size(n[1])
flat = lambda n: tuple((o, a) for p, o, a in c.sites(n))
def replace_interval(n, pos, lo, hi, rep):
    end = pos + size(n)
    if hi <= pos or end <= lo: return n
    if lo <= pos and end <= hi: return rep if pos == lo else None
    a = replace_interval(n[0], pos, lo, hi, rep); b = replace_interval(n[1], pos + size(n[0]), lo, hi, rep)
    if a is None: return b
    if b is None: return a
    return (a, b)
def g_row(t):
    assert flat(t)[648:732] == flat((pair_inc, eq))
    return replace_interval(t, 0, 648, 732, ((pair_inc, (rel, eq)), all_))
def rotate_at(t, path):
    old = c.subtree(t, path); (a, b), d = old
    return c.replace(t, path, (a, (b, d)))

out = Path(sys.argv[1]); out.mkdir(exist_ok=True)
best = None
for k in r119:
    pat = drop(g["pattern"], h_units | {k})
    t = c.replace(src, AP, assemble(pat))
    t = g_row(t)
    for rot in (False, True):
        u = rotate_at(t, "1110100100111000") if rot else t
        m = c.metrics(u)
        name = f"bc_drop{k}_{'rot' if rot else 'norot'}"
        (out / f"{name}.json").write_bytes(c.compact(c.sites(u)))
        print(name, m)
