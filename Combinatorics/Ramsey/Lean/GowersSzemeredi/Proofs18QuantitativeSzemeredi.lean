import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Sections17_18
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Auditing the quantitative deduction in Section 18

This module keeps `section18_partition_index_nonempty`; the rest of the
development, with its description, is in `Proofs18QuantitativeSzemerediSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma section18_partition_index_nonempty {N M : Nat} [NeZero N]
    (P : Fin M → Finset (ZMod N)) (hP : IsPartition P Finset.univ) :
    0 < M := by
  by_contra hM
  have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
  subst M
  obtain ⟨i, _hi⟩ := (hP.1 (0 : ZMod N)).mp (Finset.mem_univ _)
  exact Fin.elim0 i

end LeanProofs.GowersSzemeredi
