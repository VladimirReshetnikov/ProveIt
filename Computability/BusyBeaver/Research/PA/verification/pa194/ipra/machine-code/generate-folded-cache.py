#!/usr/bin/env python3
"""Generate a balanced Lean transition cache from the literal table and native labels."""
import json
from pathlib import Path
import sys

if len(sys.argv) != 4:
    raise SystemExit("usage: generate-folded-cache.py DENSE_TABLE LABELS_JSON OUTPUT")
table_path, labels_path, output = map(Path, sys.argv[1:])
labels = json.loads(labels_path.read_text())
rows = {q: [None, None] for q in labels}
for line in table_path.read_text().splitlines():
    if line.strip():
        q, b, w, d, dst = line.split()
        rows[labels[int(q)]][int(b)] = (w == "1", d == "R", labels[int(dst)])


def transition(row):
    if row is None:
        return "none"
    return "some ({},{},{})".format(str(row[0]).lower(), str(row[1]).lower(), row[2])


def tree(items, indent="  "):
    if not items:
        return ".empty"
    mid = len(items) // 2
    q, (a, b) = items[mid]
    if len(items) == 1:
        return f"(.node {q} ({transition(a)}) ({transition(b)}) .empty .empty)"
    child_indent = indent + "  "
    return (f"(.node {q} ({transition(a)}) ({transition(b)})\n"
            f"{child_indent}{tree(items[:mid], child_indent)}\n"
            f"{child_indent}{tree(items[mid+1:], child_indent)})")



output.write_text("""import PA194FoldedRuntimeRows

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194FoldedCache
open PA194FoldedRuntimeRows PA194LocalQuotient

abbrev Transition := Option (Bool × Bool × Nat)

/-- The balanced lookup used to evaluate the finite certificates. -/
inductive Tree where
  | empty
  | node (state : Nat) (zero one : Transition) (left right : Tree)

def Tree.keys : Tree → List Nat
  | .empty => []
  | .node q _ _ left right => q :: (left.keys ++ right.keys)

def Tree.read : Tree → Nat → Bool → Transition
  | .empty, _, _ => none
  | .node q zero one left right, p, b =>
    if p < q then left.read p b
    else if q < p then right.read p b
    else if b then one else zero

theorem Tree.outside (t : Tree) (q : Nat) (b : Bool) (h : q ∉ t.keys) :
    t.read q b = none := by
  induction t with
  | empty => rfl
  | node p zero one left right ihl ihr =>
    simp only [Tree.keys,List.mem_cons,List.mem_append,not_or] at h
    simp only [Tree.read]
    split
    · exact ihl h.2.1
    · split
      · exact ihr h.2.2
      · exact False.elim (h.1 (by omega))

def table : Tree :=
  """ + tree(sorted(rows.items())) + """

def cachedMachine : M6.Zip.TMN := table.read

theorem keys_match : table.keys.all labels.contains = true := by decide +kernel

theorem outside (q : Nat) (b : Bool) (h : q ∉ labels) :
    cachedMachine q b = none := by
  apply table.outside
  intro hq
  exact h (List.contains_iff_mem.mp (List.all_eq_true.mp keys_match q hq))

def agreesAt (q : Nat) : Bool := (cachedMachine q false == machine q false) &&
  (cachedMachine q true == machine q true)

def checkRows (base count : Nat) : Bool :=
  ((labels.drop base).take count).all agreesAt

theorem checkRows_sound (base count j : Nat) (hb : checkRows base count = true)
    (hlo : base ≤ j) (hhi : j < base+count) (hj : j < labels.length) :
    agreesAt labels[j] = true := by
  let part := (labels.drop base).take count
  have h : j-base < part.length := by simp [part]; omega
  have he : part[j-base] = labels[j] := by
    simp only [part,List.getElem_take,List.getElem_drop]
    congr 1
    omega
  rw [←he]
  exact List.all_eq_true.mp hb _ (List.mem_of_getElem (i := j-base) (h := h) rfl)

#print axioms keys_match
#print axioms checkRows_sound
end PA194FoldedCache
""")
