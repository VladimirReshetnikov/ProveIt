import GowersSzemeredi.Proofs16ZeroDimensionalFaces
import GowersSzemeredi.Proofs16HalfDensityFaces

/-! The half-density restriction has all proper face covers with the single
parameter required in the structured pair of Lemma 16.4. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_face_error_range (k : Nat) {theta : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < (2 : Real) ^ (-(k + 2 : Real)) * theta ∧
      (2 : Real) ^ (-(k + 2 : Real)) * theta ≤ 1 := by
  have hf : (2 : Real) ^ (-(k + 2 : Real)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hk : (0 : Real) ≤ k := Nat.cast_nonneg k
    linarith
  exact ⟨mul_pos (Real.rpow_pos_of_pos (by norm_num) _) ht,
    (mul_le_of_le_one_left ht.le hf).trans ht1⟩

theorem restrict_proper_faces_common_parameter (k : Nat)
    (hth : ∀ l, 1 ≤ l → l ≤ k → Theorem162At l) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        theta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (theta / 2) * (N : Real) ^ (k + 1) ≤ B'.card ∧
          ProperCrossSectionsMultiplyLinear gamma
            (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
            B' phi := by
  let eps := (2 : Real) ^ (-(k + 2 : Real)) * theta
  obtain ⟨heps, heps1⟩ := section16_face_error_range k ht ht1
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hr : ∀ l, 1 ≤ gamma ^ (-(2 : Int)) * multipleS eps gamma l := by
    intro l
    exact one_le_mul_of_one_le_of_one_le hginv (one_le_multipleS l heps heps1 hg hg1)
  obtain ⟨N0, hN0⟩ := restrict_proper_faces_half_density k hth gamma theta hg hg1 ht ht1
  refine ⟨N0, ?_⟩
  intro N _ _ hN B phi hB hprod
  obtain ⟨B', hsub, hcard, hfaces⟩ := hN0 N hN B phi hB hprod
  refine ⟨B', hsub, hcard, ?_⟩
  intro l hl F
  by_cases hl0 : l = 0
  · subst l
    exact multiplyLinearFunction_dimension_zero (F.domain B') (F.pullback phi) hg hg1 (hr k)
  · have hl1 : 1 ≤ l := by omega
    have hlk : l ≤ k := by omega
    apply (hfaces l hl1 hlk F).mono_parameter hg hg1 (hr l)
    exact mul_le_mul_of_nonneg_left (multipleS_mono_dimension heps heps1 hg hg1 hlk)
      (by positivity)

end LeanProofs.GowersSzemeredi
