import Mathlib.Computability.RE

/-! Isolated check of the search/RE adapter proposed for S1.
The literal program and its correctness binding are separate obligations.
This file intentionally abstracts them as `hf` and `hr`. -/

namespace GenericREAdapter

theorem search_predicate_re {f : ℕ → ℕ} (hf : Nat.Primrec f)
    {r : ℕ → Prop} (hr : ∀ n, (∃ t, f t = 1) ↔ r n) : REPred r := by
  have ht : Primrec fun v : ℕ × ℕ => decide (f v.2 = 1) :=
    (Primrec.eq.comp
      ((Primrec.nat_iff.mpr hf).comp Primrec.snd)
      (Primrec.const 1)).decide
  have hsearch : Partrec fun _ : ℕ => Nat.rfind
      (fun t => Part.some (decide (f t = 1))) :=
    Partrec.rfind ht.to_comp.partrec
  apply hsearch.dom_re.of_eq
  intro n
  simp only [Nat.rfind_dom, Part.mem_some_iff, true_eq_decide_iff,
    Part.some_dom, implies_true, and_true]
  exact hr n

#print axioms search_predicate_re

end GenericREAdapter
