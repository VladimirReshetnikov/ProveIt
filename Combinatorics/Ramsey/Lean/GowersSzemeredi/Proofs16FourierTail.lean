import GowersSzemeredi.Proofs16TrapezoidTruncation
import Mathlib.Analysis.PSeries

/-! Centered-frequency multiplicities and a finite inverse-square tail.
These estimates turn the trapezoid's Fourier decay into uniform truncation
error, without any asymptotic or infinite-series hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Sum the inverse-square weights by centered absolute value. -/
theorem centered_inverse_square_tail {N : Nat} [NeZero N] (R : Nat) :
    (∑ x ∈ Finset.univ.filter (fun x : ZMod N => R < centeredAbs x),
      (((centeredAbs x : Real)^2)⁻¹)) ≤ 4 / (R + 1 : Real) := by
  let S := Finset.univ.filter (fun x : ZMod N => R < centeredAbs x)
  let T := Finset.Ioo R (N + 1)
  have hmaps : ∀ x ∈ S, centeredAbs x ∈ T := by
    intro x hx
    have h := ZMod.natAbs_valMinAbs_le x
    have hR := (Finset.mem_filter.mp hx).2
    exact Finset.mem_Ioo.mpr ⟨hR, by dsimp [centeredAbs]; omega⟩
  have hfiber (r : Nat) : (S.filter fun x => centeredAbs x = r).card ≤ 2 := by
    have hsub : (S.filter fun x => centeredAbs x = r) ⊆
        (Finset.univ.filter fun x : ZMod N => centeredAbs x = r) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    exact (Finset.card_le_card hsub).trans (centeredAbs_fibre_card_le r)
  calc
    _ = ∑ r ∈ T, ∑ x ∈ S.filter (fun x => centeredAbs x = r),
        (((centeredAbs x : Real)^2)⁻¹) := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ r ∈ T, 2 * (((r : Real)^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ = ((S.filter fun x => centeredAbs x = r).card : Real) * (((r : Real)^2)⁻¹) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber r) (by positivity)
    _ = 2 * ∑ r ∈ T, (((r : Real)^2)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (2 / (R + 1 : Real)) :=
      mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le R (N + 1)) (by norm_num)
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
