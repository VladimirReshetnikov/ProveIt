import OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J]

noncomputable def realLinearCharacter (ω x : J → ℝ) : ℂ :=
  CircleFourier.character ((∑ j, ω j * x j : ℝ) : CircleFourier.Circle)

theorem realLinearCharacter_norm (ω x : J → ℝ) : ‖realLinearCharacter ω x‖ = 1 :=
  CircleFourier.norm_character _

theorem realLinearCharacter_lipschitz (ω : J → ℝ) (W : ℝ≥0)
    (hW : ∀ j, |ω j| ≤ W) :
    LipschitzWith (CircleFourier.characterLipConstant * (Fintype.card J * W))
      (realLinearCharacter ω) := by
  have hlin : LipschitzWith (Fintype.card J * W) (fun x : J → ℝ => ∑ j, ω j * x j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |ω j * x j - ω j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J, (W : ℝ) * dist x y := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul (hW j) (by simpa only [Real.dist_eq] using dist_le_pi_dist x y j)
          (abs_nonneg _) W.coe_nonneg
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_natCast]; ring
  have hquot : LipschitzWith 1 (fun x : ℝ => (x : CircleFourier.Circle)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← AddCircle.coe_sub, NNReal.coe_one, one_mul, dist_eq_norm]
    exact QuotientAddGroup.norm_mk_le_norm
  have hc := CircleFourier.character_lipschitz.comp (hquot.comp hlin)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_mul, Function.comp_def, realLinearCharacter] using hc.dist_le_mul x y

noncomputable def plateauFourierMode (H : ℝ) (ω x : J → ℝ) : ℂ :=
  (normalizedSupportPlateau H x : ℂ) * realLinearCharacter ω x

theorem plateauFourierMode_norm (H : ℝ) (ω x : J → ℝ) : ‖plateauFourierMode H ω x‖ ≤ 1 := by
  rw [plateauFourierMode, norm_mul, realLinearCharacter_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (normalizedSupportPlateau_range H x).1]
  exact (normalizedSupportPlateau_range H x).2

theorem plateauFourierMode_lipschitz (H : ℝ) (ω : J → ℝ) (W : ℝ≥0)
    (hW : ∀ j, |ω j| ≤ W) :
    LipschitzWith (CircleFourier.characterLipConstant * (Fintype.card J * W) + 4)
      (plateauFourierMode H ω) := by
  have hp : LipschitzWith 4 (fun x : J → ℝ => (normalizedSupportPlateau H x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
      (normalizedSupportPlateau_lipschitz (J := J) H).dist_le_mul x y
  have hc := lipschitz_mul_of_bounds (fun x : J → ℝ => (normalizedSupportPlateau H x : ℂ))
      (realLinearCharacter ω) hp (realLinearCharacter_lipschitz ω W hW)
      (Bf := 1) (Bg := 1)
      (fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg (normalizedSupportPlateau_range H x).1]
        exact (normalizedSupportPlateau_range H x).2)
      (fun x => (realLinearCharacter_norm ω x).le)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_mul, plateauFourierMode] using hc.dist_le_mul x y

noncomputable def rationalGridPhase (D : ℕ) [NeZero D] (a : J → ℤ) (r : J → ZMod D) : ℂ :=
  CircleFourier.character (ZMod.toAddCircle (∑ j, (a j : ZMod D) * r j))

theorem rationalGridPhase_norm (D : ℕ) [NeZero D] (a : J → ℤ) (r : J → ZMod D) :
    ‖rationalGridPhase D a r‖ = 1 := CircleFourier.norm_character _

theorem rationalGridPhase_intCast (D : ℕ) [NeZero D] (a z : J → ℤ) :
    rationalGridPhase D a (integerGridResidue D z) =
      realLinearCharacter (fun j => (a j : ℝ) / D) (fun j => (z j : ℝ)) := by
  have he : (∑ j, (a j : ZMod D) * (z j : ZMod D)) = ((∑ j, a j * z j : ℤ) : ZMod D) := by
    simp only [Int.cast_sum, Int.cast_mul]
  unfold rationalGridPhase integerGridResidue realLinearCharacter
  rw [he, ZMod.toAddCircle_intCast]
  congr 2
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem plateau_grid_character_split (H : ℝ) {K M D : ℕ} [NeZero M] [NeZero D]
    (hK : 0 < K) (k : J → Fin M) (a : J → ℤ) (ω : J → ℝ)
    (hfreq : ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K)
    (shift z : J → ℤ) :
    (normalizedSupportPlateau H (fun j => ((z j : ℝ) - shift j) / K) : ℂ) *
        (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)) =
      rationalGridPhase D a (integerGridResidue D (shift - z)) *
        plateauFourierMode H (fun j => -ω j) (fun j => ((z j : ℝ) - shift j) / K) := by
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hphase : (∑ j, ((k j).val : ℝ) / M * ((shift j : ℝ) - z j)) =
      (∑ j, (a j : ℝ) / D * ((shift j : ℝ) - z j)) +
        ∑ j, -ω j * (((z j : ℝ) - shift j) / K) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hfreq j]
    field_simp [hK0]
    ring
  rw [← rectangularGridCharacter_sub, rectangularGridCharacter_eq,
    rationalGridPhase_intCast, plateauFourierMode]
  simp only [realLinearCharacter, Pi.sub_apply, Int.cast_sub]
  rw [hphase, AddCircle.coe_add, CircleFourier.character_add]
  ring

end Erdos3

end

end OAI
