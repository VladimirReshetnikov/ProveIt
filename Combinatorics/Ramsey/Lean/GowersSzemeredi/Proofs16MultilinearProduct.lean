import GowersSzemeredi.Proofs16ProductEndpoint
import GowersSzemeredi.Proofs14Product

/-! This module keeps `IsMultilinear.linearOn_coordinate`; the rest of the
development, with its description, is in `Proofs16MultilinearProductSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IsMultilinear.linearOn_coordinate {N k : Nat} [NeZero N]
    {phi : Point N k → ZMod N} (h : IsMultilinear phi) (y : Point N k) (j : Fin k) :
    LinearOn Finset.univ (coordinateRestriction phi y j) := by
  obtain ⟨c, hc⟩ := h
  let a : (Fin k → Bool) → ZMod N := fun e =>
    ∏ i ∈ Finset.univ.erase j, if e i then y i else 1
  have hp (e : Fin k → Bool) (x : ZMod N) :
      (∏ i, if e i then replaceCoordinate y j x i else 1) =
        a e * (if e j then x else 1) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp [replaceCoordinate, Function.update_of_ne (Finset.mem_erase.mp hi).1]
    · simp [replaceCoordinate]
  refine ⟨∑ e, if e j then c e * a e else 0,
    ∑ e, if e j then 0 else c e * a e, fun x _ => ?_⟩
  unfold coordinateRestriction
  rw [hc, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [hp]
  cases e j <;> simp [mul_assoc]

end LeanProofs.GowersSzemeredi
