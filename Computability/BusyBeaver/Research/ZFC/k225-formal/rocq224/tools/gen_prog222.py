"""Write the program layer for dag222 (K230's Dag230 with the AX node 236 rebuilt by
make_dag222.py): Dag222.v from dag222_nodes.json, and forks of Elliot's ProgLib230 and L2Root230
(Dag230 -> Dag222, dag230 -> dag222, Enum230 -> Enum222)."""
import json, re
from pathlib import Path

S = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad\k224rocq")
V = S.parent / "rocq225/pkg/vendor/k230-rocq/coq/prog"
OUT = S / "src"
d = json.load(open(S / "dag222_nodes.json"))
nn = d["nnodes"]


def ed(e):
    op, a = e
    if op == "N":
        return f"ENode {a}"
    return op if a is None else f"{op} {a}"


# Dag222.v, in Dag230.v's layout
lines = ["(** dag222: K230's Dag230 (reconstructed frozen source with the QT loop rotation) with the",
         "    AX node 236 rebuilt for the seed-K 222 by tools/make_dag222.py: the rho7 row word becomes",
         "    the merged equality row G, and the bundle word the helper-free seed bundle. Nodes 0-300",
         "    other than 236 are Dag230's; 301-" + str(nn - 1) + " continue node 236's word. *)",
         "From K230 Require Import RM.",
         "Definition dag_nodes (n : nat) : edge * edge :=",
         "  match n with"]
nodes = {int(k): v for k, v in d["nodes"].items()}
assert sorted(nodes) == list(range(nn)), (min(nodes), max(nodes), nn)
old = {}
for line in open(V / "Dag230.v", encoding="utf-8"):
    m = re.match(r"\s*\|\s*(\d+)\s*=>\s*\((.*)\)\s*$", line)
    if m:
        old[int(m.group(1))] = m.group(2).replace(" ", "")
for n in range(nn):
    a, b = nodes[n]
    s = f"({ed(a)}, {ed(b)})"
    if n < 301 and n != 236:
        assert s.replace(" ", "") == "(" + old[n] + ")", (n, s, old[n])
    lines.append(f"  | {n} => {s}")
lines += ["  | _ => (EHalt, EHalt)", "  end.", f"Definition dag222 : prog := mkProg dag_nodes 0 {nn}.", ""]
(OUT / "Dag222.v").write_text("\n".join(lines), encoding="utf-8", newline="\n")


def fork(src, dst, header, pairs):
    t = (V / src).read_text(encoding="utf-8")
    for a, b in pairs:
        n = len(re.findall(a, t))
        assert n > 0, (src, a)
        t = re.sub(a, b, t)
    (OUT / dst).write_text(header + t, encoding="utf-8", newline="\n")


H = "(** Forked by gen_prog222.py from Elliot Glazer's k230-rocq (3142e4d) prog/{0} for dag222. *)\n"
fork("ProgLib230.v", "ProgLib222.v", H.format("ProgLib230.v"),
     [(r"From K230P Require Import Dag230\.", "From K224 Require Import Dag222."),
      (r"\bdag230\b", "dag222")])
fork("L2Root230.v", "L2Root222.v", H.format("L2Root230.v"),
     [(r"From K230P Require Import Dag230 ProgLib230\.", "From K224 Require Import Dag222 ProgLib222."),
      (r"From K230L Require Import Codes230 Enum230\.",
       "From K230L Require Import Codes230.\nFrom K224 Require Import Codes222 Enum222."),
      (r"Enum230\.", "Enum222."),
      (r"\bdag230\b", "dag222")])
print("Dag222.v:", nn, "nodes; ProgLib222.v, L2Root222.v written")
