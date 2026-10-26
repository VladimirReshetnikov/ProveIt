import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic

/-! Preserve simultaneous zeros under an elementary row addition.
The intended concrete application is SplitCertificate59, where only
rows 13 and 14 are modified by adding rows 1 and 2 respectively. -/

namespace ProofSimplification.RowOperations

variable {ι R : Type*} [DecidableEq ι] [AddZeroClass R]

def addAt (dst src : ι) (r : ι → R) (k : ι) : R :=
  if k = dst then r dst + r src else r k

theorem forall_addAt_eq_zero_iff (dst src : ι) (h : dst ≠ src) (r : ι → R) :
    (∀ k, addAt dst src r k = 0) ↔ ∀ k, r k = 0 := by
  constructor
  · intro hz k
    have hsrc : r src = 0 := by
      simpa only [addAt, if_neg h.symm] using hz src
    by_cases hk : k = dst
    · subst k
      simpa only [addAt, hsrc, add_zero, ite_self] using hz dst
    · simpa only [addAt, if_neg hk] using hz k
  · intro hz k
    simp only [addAt, hz, add_zero, ite_self]

omit [DecidableEq ι] in
/-- A surjective reordering preserves all zero constraints. -/
theorem forall_reindex_eq_zero_iff {κ : Type*} (f : κ → ι)
    (hf : Function.Surjective f) (r : ι → R) :
    (∀ k, r (f k) = 0) ↔ ∀ k, r k = 0 := (hf.forall (p := fun k => r k = 0)).symm

#print axioms forall_addAt_eq_zero_iff
#print axioms forall_reindex_eq_zero_iff

end ProofSimplification.RowOperations
