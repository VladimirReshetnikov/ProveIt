import GowersSzemeredi.Proofs16BohrDenseDifference
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Convert a weighted missing-point estimate into Bohr difference
containment, with a rank-only sufficient budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_weighted_defect_sub_cover {N : Nat} [NeZero N]
    (K A : Finset (ZMod N)) {rho weight budget : Real}
    (hrho : 0 < rho) (hw : 0 < weight)
    (hmiss : (((bohr K rho) \ A).card : Real) * weight ≤ budget)
    (hbudget : (4 : Real)^(K.card + 1) * budget ≤ (bohr K rho).card * weight)
    (d : ZMod N) (hd : d ∈ bohr K (rho / 2)) :
    ∃ x ∈ A, ∃ y ∈ A, d = x - y := by
  have hmul : ((4^(K.card + 1) * ((bohr K rho) \ A).card : Nat) : Real) * weight ≤
      (bohr K rho).card * weight := by
    calc
      _ = (4 : Real)^(K.card + 1) * ((((bohr K rho) \ A).card : Real) * weight) := by
        push_cast
        ring
      _ ≤ (4 : Real)^(K.card + 1) * budget :=
        mul_le_mul_of_nonneg_left hmiss (by positivity)
      _ ≤ _ := hbudget
  have hcard : 4^(K.card + 1) * ((bohr K rho) \ A).card ≤ (bohr K rho).card := by
    exact_mod_cast le_of_mul_le_mul_right hmul hw
  exact bohr_dense_sub_cover K hrho A hcard d hd

/-- A sufficient defect budget involving only the rank cap and a Bohr
cell count, independent of the modulus and actual Bohr cardinality. -/
theorem bohr_weighted_defect_sub_cover_rank {N Q r : Nat} [NeZero N] [NeZero Q]
    (K A : Finset (ZMod N)) {rho weight loss : Real}
    (hrho : 0 < rho) (hw : 0 < weight) (hloss : 0 ≤ loss)
    (hK : K.card ≤ r) (hQ : 1 ≤ rho * Q)
    (hmiss : (((bohr K rho) \ A).card : Real) * weight ≤ loss * N)
    (hbudget : (4 : Real)^(r + 1) * loss * (Q : Real)^r ≤ weight)
    (d : ZMod N) (hd : d ∈ bohr K (rho / 2)) :
    ∃ x ∈ A, ∃ y ∈ A, d = x - y := by
  apply bohr_weighted_defect_sub_cover K A hrho hw hmiss _ d hd
  have hQc : (Q : Real)^K.card ≤ (Q : Real)^r := by
    exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) hK
  have hfour : (4 : Real)^(K.card + 1) ≤ (4 : Real)^(r + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hK 1)
  have hN : (N : Real) ≤ (Q : Real)^r * (bohr K rho).card := by
    have hlow : (N : Real) ≤ (Q : Real)^K.card * (bohr K rho).card := by
      exact_mod_cast bohr_card_lower K Q hQ
    exact hlow.trans (mul_le_mul_of_nonneg_right hQc (by positivity))
  calc (4 : Real)^(K.card + 1) * (loss * N)
      ≤ (4 : Real)^(r + 1) * (loss * N) := mul_le_mul_of_nonneg_right hfour (by positivity)
    _ ≤ (4 : Real)^(r + 1) * (loss * ((Q : Real)^r * (bohr K rho).card)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN hloss) (by positivity)
    _ = ((4 : Real)^(r + 1) * loss * (Q : Real)^r) * (bohr K rho).card := by ring
    _ ≤ weight * (bohr K rho).card := mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = (bohr K rho).card * weight := by ring

end LeanProofs.GowersSzemeredi
