import BusyBeaver.ZFC.RMDag

/-!
Transfer of runs between two register programs that agree on a closed set of nodes.

A set of nodes `ok` is *closed* for `p` and `q` when each of its nodes either has the same
content in both programs, with both children leaves or nodes of the set, or carries a contract:
every run of `p` from it is a run of `q`. Then every run of `p` from a leaf or a node of the set
is a run of `q` (`run_transfer`), by induction on the run: a contract node is used whole, any
other node is rebuilt from its children.
-/

namespace SetTheory.BusyBeaver.ZFC.RMTransfer

open RMDag

/-- The edge is a leaf or a node of `ok`. -/
def inside (ok : Nat → Bool) : Edge → Bool
  | .node m => ok m
  | _ => true

/-- `ok` is closed for `p` and `q`. -/
def Closed (p q : Prog) (ok : Nat → Bool) : Prop :=
  ∀ n, ok n = true →
    (p.nodes n = q.nodes n ∧ inside ok (p.nodes n).1 = true ∧ inside ok (p.nodes n).2 = true) ∨
    (∀ R x R', Run p (.node n) R x R' → Run q (.node n) R x R')

/-- A bounded set whose nodes all agree is closed. -/
theorem closed_of_bounded {p q : Prog} {ok : Nat → Bool} {N : Nat} (hN : ∀ n, ok n = true → n < N)
    (h : ∀ n < N, ok n = true →
      p.nodes n = q.nodes n ∧ inside ok (p.nodes n).1 = true ∧ inside ok (p.nodes n).2 = true) :
    Closed p q ok :=
  fun n hn => Or.inl (h n (hN n hn) hn)

/-- So is one whose nodes agree except a contract node. -/
theorem closed_of_contract {p q : Prog} {ok : Nat → Bool} {N n0 : Nat}
    (hN : ∀ n, ok n = true → n < N)
    (h : ∀ n < N, ok n = true → n ≠ n0 →
      p.nodes n = q.nodes n ∧ inside ok (p.nodes n).1 = true ∧ inside ok (p.nodes n).2 = true)
    (h0 : ∀ R x R', Run p (.node n0) R x R' → Run q (.node n0) R x R') : Closed p q ok := by
  intro n hn
  by_cases e : n = n0
  · subst e; exact Or.inr h0
  · exact Or.inl (h n (hN n hn) hn e)

section

variable {p q : Prog} {ok : Nat → Bool} (hc : Closed p q ok)
include hc

/-- Runs from inside a closed set transfer from `p` to `q`. -/
theorem run_transfer {e : Edge} {R : Regs} {x : Exit} {R' : Regs} (h : Run p e R x R') :
    inside ok e = true → Run q e R x R' := by
  induction h with
  | inc r R => exact fun _ => .inc r R
  | decPos r R v hv => exact fun _ => .decPos r R v hv
  | decZero r R hz => exact fun _ => .decZero r R hz
  | brk0 R => exact fun _ => .brk0 R
  | brkS k R => exact fun _ => .brkS k R
  | contS k R => exact fun _ => .contS k R
  | halt R => exact fun _ => .halt R
  | carBrk1 n R R' h ih =>
      intro hb; rcases hc n hb with ⟨e, h1, -⟩ | hn
      · exact .carBrk1 _ _ _ (e ▸ ih h1)
      · exact hn _ _ _ (.carBrk1 _ _ _ h)
  | carBrkS n k R R' h ih =>
      intro hb; rcases hc n hb with ⟨e, h1, -⟩ | hn
      · exact .carBrkS _ _ _ _ (e ▸ ih h1)
      · exact hn _ _ _ (.carBrkS _ _ _ _ h)
  | carCont n k R R' h ih =>
      intro hb; rcases hc n hb with ⟨e, h1, -⟩ | hn
      · exact .carCont _ _ _ _ (e ▸ ih h1)
      · exact hn _ _ _ (.carCont _ _ _ _ h)
  | carHalt n R R' h ih =>
      intro hb; rcases hc n hb with ⟨e, h1, -⟩ | hn
      · exact .carHalt _ _ _ (e ▸ ih h1)
      · exact hn _ _ _ (.carHalt _ _ _ h)
  | cdrNormal n R R1 R' h1 h2 ih1 ih2 =>
      intro hb; rcases hc n hb with ⟨e, c1, c2⟩ | hn
      · exact .cdrNormal _ _ _ _ (e ▸ ih1 c1) (e ▸ ih2 c2)
      · exact hn _ _ _ (.cdrNormal _ _ _ _ h1 h2)
  | cdrBrk n k R R1 R' h1 h2 ih1 ih2 =>
      intro hb; rcases hc n hb with ⟨e, c1, c2⟩ | hn
      · exact .cdrBrk _ _ _ _ _ (e ▸ ih1 c1) (e ▸ ih2 c2)
      · exact hn _ _ _ (.cdrBrk _ _ _ _ _ h1 h2)
  | cdrCont1 n R R1 R2 R' x h1 h2 h3 ih1 ih2 ih3 =>
      intro hb; rcases hc n hb with ⟨e, c1, c2⟩ | hn
      · exact .cdrCont1 _ _ _ _ _ _ (e ▸ ih1 c1) (e ▸ ih2 c2) (ih3 hb)
      · exact hn _ _ _ (.cdrCont1 _ _ _ _ _ _ h1 h2 h3)
  | cdrContS n k R R1 R' h1 h2 ih1 ih2 =>
      intro hb; rcases hc n hb with ⟨e, c1, c2⟩ | hn
      · exact .cdrContS _ _ _ _ _ (e ▸ ih1 c1) (e ▸ ih2 c2)
      · exact hn _ _ _ (.cdrContS _ _ _ _ _ h1 h2)
  | cdrHalt n R R1 R' h1 h2 ih1 ih2 =>
      intro hb; rcases hc n hb with ⟨e, c1, c2⟩ | hn
      · exact .cdrHalt _ _ _ _ (e ▸ ih1 c1) (e ▸ ih2 c2)
      · exact hn _ _ _ (.cdrHalt _ _ _ _ h1 h2)

/-- A node of a closed set runs alike in both programs. -/
theorem node_transfer {n : Nat} (hn : ok n = true) {R : Regs} {x : Exit} {R' : Regs}
    (h : Run p (.node n) R x R') : Run q (.node n) R x R' :=
  run_transfer hc h hn

/-- So does iterating a root of the set. -/
theorem iter_transfer (hroot : p.root = q.root) (hr : ok p.root = true) {R : Regs}
    (h : IterHalts p R) : IterHalts q R := by
  induction h with
  | halt R R' h => exact .halt R R' (hroot ▸ node_transfer hc hr h)
  | next R R' h _ ih => exact .next R R' (hroot ▸ node_transfer hc hr h) ih

end

/-- A contract node: `p` runs it as `q` does when both runs are total and deterministic. -/
theorem contract {p q : Prog} {n : Nat} (out : Regs → Exit) (res : Regs → Regs)
    (hp : ∀ R, Run p (.node n) R (out R) (res R)) (hq : ∀ R, Run q (.node n) R (out R) (res R)) :
    ∀ R x R', Run p (.node n) R x R' → Run q (.node n) R x R' := by
  intro R x R' h
  obtain ⟨rfl, rfl⟩ := run_det h (hp R)
  exact hq R

end SetTheory.BusyBeaver.ZFC.RMTransfer
