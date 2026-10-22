#!/usr/bin/env python3
"""Compute the exact closed macro support and emit a Rocq binding.

This independent finite check is supplemental. K215MacroSlice.v proves the
literal checks inside Rocq; the generator and this parser are not trusted.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("repo", type=Path)
parser.add_argument("--output", type=Path, default=Path(__file__).parent)
args = parser.parse_args()
base = args.repo / "Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq"
out = args.output
out.mkdir(parents=True, exist_ok=True)

def read_table(path):
    text = path.read_text()
    rows = {}
    for n, a, b in re.findall(r"\| (\d+) => \(([^,]+), ([^)]+)\)", text):
        assert int(n) not in rows
        rows[int(n)] = (a.strip(), b.strip())
    assert rows and set(rows) == set(range(len(rows)))
    assert "| _ => (EHalt, EHalt)" in text
    return rows

paths = {"perm": base / "215/DagPerm.v", "dom": base / "217/DagDom.v", "219": base / "218/Dag219.v"}
tables = {name: read_table(p) for name, p in paths.items()}
lib = base / "215/ProgLibPerm.v"
roots = sorted({int(n) for n in re.findall(r"sem \(ENode (\d+)\)", lib.read_text())})
seen, todo = set(), list(roots)
while todo:
    n = todo.pop()
    if n in seen:
        continue
    seen.add(n)
    for edge in tables["perm"][n]:
        m = re.fullmatch(r"ENode (\d+)", edge)
        if m:
            todo.append(int(m.group(1)))
support = sorted(seen)
assert set(roots) <= set(support)
for name, table in tables.items():
    assert all(table[n] == tables["perm"][n] for n in support), name

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

audit = {
    "review_commit": "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95",
    "root_extraction": "All literal sem (ENode n) occurrences in ProgLibPerm.v, including tactic patterns",
    "roots": roots, "root_count": len(roots),
    "closed_support": support, "support_count": len(support),
    "agreement": {name: True for name in tables},
    "dag_rows": {name: len(t) for name, t in tables.items()},
    "files": {str(p.relative_to(args.repo)): sha(p) for p in [lib, *paths.values()]},
    "scope": "Structured RM.run for all natural-valued register files and all exits; no whole-program or binary-TM equivalence inferred",
}
normalized_bodies = {}
for variant, name in [("215", "ProgLibPerm"), ("217", "ProgLibDom"), ("218", "ProgLib219")]:
    path = base / variant / (name + ".v")
    text = path.read_text()
    body = text[text.index("From Coq Require Import"):]
    body = re.sub(r"K(?:215|217|218)F", "KXXXF", body)
    body = re.sub(r"Dag(?:Perm|Dom|219)", "DagShared", body)
    body = re.sub(r"dag(?:Perm|Dom|219)", "dagShared", body)
    normalized_bodies[variant] = {
        "source_lines": len(text.splitlines()), "source_bytes": len(text.encode()),
        "body_lines": len(body.splitlines()), "body_bytes": len(body.encode()),
        "normalized_body_sha256": hashlib.sha256(body.encode()).hexdigest(),
    }
assert len({r["normalized_body_sha256"] for r in normalized_bodies.values()}) == 1
audit["macro_library_duplicates"] = normalized_bodies
(out / "slice_audit.json").write_text(json.dumps(audit, indent=2) + "\n")

nums = lambda ns: "; ".join(map(str, ns))
v = f'''(** Generated untrusted support; all finite claims checked below. *)
From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import DagPerm.
From K217F Require Import DagDom.
From K218F Require Import Dag219.
Require Import RMSlice.
Import ListNotations.

Definition macro_roots : list nat := [{nums(roots)}].
Definition macro_support : list nat := [{nums(support)}].

Lemma perm_dom_slice : check_slice dagPerm dagDom macro_support = true.
Proof. vm_compute. reflexivity. Qed.

Lemma perm_219_slice : check_slice dagPerm dag219 macro_support = true.
Proof. vm_compute. reflexivity. Qed.

Lemma macro_roots_covered :
  forallb (fun n => allowedb macro_support (ENode n)) macro_roots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma root_allowed n : In n macro_roots -> allowed macro_support (ENode n).
Proof.
  intro Hn. apply allowedb_sound.
  exact (proj1 (forallb_forall _ _) macro_roots_covered n Hn).
Qed.

Theorem macro_run_215_217 n R x R' : In n macro_roots ->
  (run dagPerm (ENode n) R x R' <-> run dagDom (ENode n) R x R').
Proof.
  intro Hn. exact (checked_run_iff _ _ _ perm_dom_slice _ _ _ _ (root_allowed n Hn)).
Qed.

Theorem macro_run_215_218 n R x R' : In n macro_roots ->
  (run dagPerm (ENode n) R x R' <-> run dag219 (ENode n) R x R').
Proof.
  intro Hn. exact (checked_run_iff _ _ _ perm_219_slice _ _ _ _ (root_allowed n Hn)).
Qed.

Print Assumptions macro_run_215_217.
Print Assumptions macro_run_215_218.
'''
(out / "K215MacroSlice.v").write_text(v)
print(json.dumps({"roots": len(roots), "support": len(support), "agree": list(tables)}, indent=2))
