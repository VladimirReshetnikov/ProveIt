import GowersSzemeredi.Proofs13EndpointNormalization
import GowersSzemeredi.Sections12_13

/-! Transfer normalized derivative errors to the paper's unnormalized
Fourier coefficients, uniformly in directions and frequencies. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem fourier_norm_sub_le_L1 {N : Nat} [NeZero N] (f g : ZMod N → Complex) (r : ZMod N) :
    ‖fourier f r - fourier g r‖ ≤ (N : Real) * endpointL1Distance f g := by
  unfold fourier
  rw [ZMod.dft_apply, ZMod.dft_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : ZMod N, ‖ZMod.stdAddChar (-(x * r)) • f x - ZMod.stdAddChar (-(x * r)) • g x‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod N, ‖f x - g x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← smul_sub, smul_eq_mul, norm_mul, AddChar.norm_apply, one_mul]
    _ = _ := by
      unfold endpointL1Distance
      rw [← Fintype.card_mul_expect]
      simp only [ZMod.card]

theorem secondDifferenceFourier_unitPhase_error {N d : Nat} [NeZero N]
    (f : ZMod N → Complex) (hf : DiscValued f) (epsilon : Real)
    (hnear : 1 - epsilon ≤ endpointCubeMean f d) (k l r : ZMod N) :
    ‖secondDifferenceFourier f k l r -
      secondDifferenceFourier (fun x => endpointUnitPhase (f x)) k l r‖ ≤ 4 * epsilon * (N : Real) := by
  have hdist := (endpoint_unitPhase_normalization f hf epsilon hnear).1
  have ht := endpointL1Distance_iteratedDifference f (fun x => endpointUnitPhase (f x)) hf
    (endpointUnitPhase_discValued f) [l, k]
  have hd : endpointL1Distance (secondDifference f k l)
      (secondDifference (fun x => endpointUnitPhase (f x)) k l) ≤ 4 * epsilon := by
    have hh : endpointL1Distance (secondDifference f k l)
        (secondDifference (fun x => endpointUnitPhase (f x)) k l) ≤
        4 * endpointL1Distance f (fun x => endpointUnitPhase (f x)) := by
      have h4 : (2 : Real) ^ ([l, k] : List (ZMod N)).length = 4 := by norm_num
      rw [h4] at ht
      exact ht
    linarith only [hh, hdist]
  have hn : (0 : Real) ≤ N := Nat.cast_nonneg _
  exact (fourier_norm_sub_le_L1 _ _ r).trans
    ((mul_le_mul_of_nonneg_left hd hn).trans_eq (by ring))

end LeanProofs.GowersSzemeredi
