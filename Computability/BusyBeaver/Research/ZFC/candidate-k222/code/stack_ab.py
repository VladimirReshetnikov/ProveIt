"""Stack Source 127's conditional root (A) with the merged-equality 223's G row (B).

Host: A's 223 table and source (K labels). Target: the grafted source (B's source with A's
changed subtrees). Changed nodes are compiled exactly as in B's construct_g226.py: a node reuses
its same-path A state when that old node is dead and the state is single-role, otherwise gets a
fresh label; leaf rows come from the existing dispatch actions; every compound decoder entry is
then checked by tape simulation. Then B's two source-dependent folds are applied, with B's fresh
labels mapped through the nodes they serve in B's parent226.
Usage: stack_ab.py A_TABLE A_SITES B_PARENT226 B_SITES226 B_FOLDS COMBINED_SITES OUT_PREFIX"""
import json, sys
from collections import Counter
from pathlib import Path

S = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad")
sys.path.insert(0, str(S / "intake179/fresh/K225_Construction_2026-10-19/K225_Construction_2026-10-19/portable/baseline226/verification"))
sys.path.insert(0, str(S / "intake181/fresh/K224_Construction_2026-10-20/K224_Construction_2026-10-20/portable/verification"))
import reconstruct227 as c
import construct_rel225 as cr

AT, AS, BP, BPS, BF, CS, OUT = sys.argv[1:8]
table = cr.read_table(Path(AT))
old_src = c.tree(json.loads(Path(AS).read_text()))
new_src = c.tree(json.loads(Path(CS).read_text()))
groups, paths = cr.decoder_map(c, table, old_src)
node_state = {v: k for k, vs in groups.items() for v in vs}

# origins: new node at path p whose A node at p differs
origins = {}
def walk(n, o, p):
    if c.leaf(n) or o is None or c.leaf(o):
        return
    if n != o:
        origins.setdefault(n, o)
    walk(n[0], o[0], p + "0"); walk(n[1], o[1], p + "1")
walk(new_src, old_src, "")
live = set()
def live_visit(n):
    if n in live or c.leaf(n):
        return
    live.add(n); live_visit(n[0]); live_visit(n[1])
live_visit(new_src)
origins = {n: o for n, o in origins.items() if o not in live}

compiled = table.copy(); mapped = dict(node_state); mapped[new_src] = 84
fresh = 300; claimed = {84: new_src}; reused = 0
def compile_node(n):
    global fresh, reused
    if n in mapped:
        return mapped[n]
    if n in origins and origins[n] in node_state and len(groups[node_state[origins[n]]]) == 1 \
            and node_state[origins[n]] not in claimed:
        k = node_state[origins[n]]; reused += 1
    else:
        k = fresh; fresh += 1
    mapped[n] = k; claimed[k] = n
    for bit, ch in enumerate(n):
        if not c.leaf(ch):
            compiled[k, bit] = (bit, 1, compile_node(ch)); continue
        if n in origins and origins[n] in node_state and origins[n][bit] == ch:
            compiled[k, bit] = table[node_state[origins[n]], bit]; continue
        choices = Counter(table[s, bit] for v, s in node_state.items() if v[bit] == ch)
        direct = [a for a, _ in choices.items() if a[:2] == (bit, 1)]
        if len(direct) == 1: compiled[k, bit] = direct[0]
        elif ch == ("CC", 1) and bit == 1: compiled[k, bit] = (0, -1, 1)
        elif ch == ("CC", 2) and bit == 1: compiled[k, bit] = (0, -1, 16)
        elif ch == ("CB", 1) and bit == 1: compiled[k, bit] = (0, -1, 40)
        else: raise ValueError(("No primitive dispatch", ch, bit, choices))
    return k
for bit, ch in enumerate(new_src):
    compiled[84, bit] = (bit, 1, compile_node(ch))

def prune(T):
    reach = {0}; todo = [0]
    for q in todo:
        for b in (0, 1):
            z = T[q, b][2]
            if z != 254 and z not in reach:
                reach.add(z); todo.append(z)
    return {r: a for r, a in T.items() if r[0] in reach}
compiled = prune(compiled)
g2, _ = cr.decoder_map(c, compiled, new_src)   # raises if any compound entry is wrong
print("compiled:", len(compiled) // 2, "states; fresh labels", fresh - 300, "reused", reused)
Path(OUT + "_prefold.k.tm").write_bytes(cr.encode_table(compiled))

# map B's fresh fold labels through the nodes they serve in B's parent226
btab = cr.read_table(Path(BP)); bsrc = c.tree(json.loads(Path(BPS).read_text()))
bg, _ = cr.decoder_map(c, btab, bsrc)
inv = {}
for k, vs in g2.items():
    for v in vs:
        inv[v] = k
T = dict(compiled)
for f in json.load(open(BF))["folds"]:
    keep, dele = f["keep"], f["delete"]
    if (dele, 0) not in btab or dele < 300:
        if (dele, 0) in T:
            print("fold", keep, "<-", dele, ": deleted state still present, applying as is")
        else:
            print("fold", keep, "<-", dele, ": already applied in host"); continue
        d2 = dele
    else:
        nodes = bg[dele]
        cand = {inv.get(v) for v in nodes}
        print("fold", keep, "<-", dele, ": B's state serves", len(nodes), "nodes; here served by", cand)
        if len(cand) != 1 or None in cand:
            print("   cannot map; skipped"); continue
        (d2,) = cand
    if (keep, 0) not in T:
        print("   keep state", keep, "absent; skipped"); continue
    for r, (w, d, z) in list(T.items()):
        if z == d2:
            T[r] = (w, d, keep)
    T[keep, 0] = tuple(f["a0"]); T[keep, 1] = tuple(f["a1"])
    T.pop((d2, 0)); T.pop((d2, 1))
    T = prune(T)
    print("   applied:", len(T) // 2, "states")
Path(OUT + ".k.tm").write_bytes(cr.encode_table(T))
print("final:", len(T) // 2, "states")
