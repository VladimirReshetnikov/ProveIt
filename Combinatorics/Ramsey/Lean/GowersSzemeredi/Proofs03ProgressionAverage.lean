import GowersSzemeredi.Proofs03LinearPatternBound

/-!
# The generalized von Neumann bound for arithmetic progressions

The progression estimate specializes the bound for distinct coefficients to
the coefficients `0, …, k - 1`. The hypothesis `k ≤ N` makes those residues
distinct, retaining the corrected prime-modulus form of Theorem 3.2.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Theorem 3.2.** Generalized von Neumann bound for progression averages,
in the corrected prime-modulus range `2 ≤ k ≤ N`. -/
theorem theorem_3_2_holds : theorem_3_2 := by
  intro N k _ _ hk2 hkN f hf alpha ha0 hu
  have hc : Function.Injective (fun i : Fin k => ((i : Nat) : ZMod N)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg ZMod.val hij
    simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hkN),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hkN)] using hv
  change ‖linearPatternAverage (fun i : Fin k => ((i : Nat) : ZMod N)) f‖ ≤ _
  exact linearPattern_uniform_last_bound hk2 (fun i : Fin k => ((i : Nat) : ZMod N))
    hc f hf alpha ha0 hu

end LeanProofs.GowersSzemeredi
