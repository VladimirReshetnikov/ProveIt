import GowersSzemeredi.Proofs15DegenerateRange

/-! Declarations of `Proofs15DegenerateRange` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

theorem isDegenerateWithin_one_iff {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) : R.IsDegenerateWithin 1 ↔ R.IsDegenerate := by
  constructor
  · rintro ⟨eta, hb, hn, hm⟩
    refine ⟨eta, ?_, hn, hm⟩
    rintro ⟨e, j⟩
    have := hb e j
    push_cast at this
    show eta e j = -1 ∨ eta e j = 0 ∨ eta e j = 1
    omega
  · rintro ⟨eta, ht, hn, hm⟩
    refine ⟨eta, ?_, hn, hm⟩
    intro e j
    rcases ht (e, j) with h | h | h <;> simp only at h <;> rw [h] <;> norm_num

end LeanProofs.GowersSzemeredi
