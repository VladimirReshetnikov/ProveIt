import OAI.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
import OAI.Combinatorics.Progressions.Sampling.SquareSamplingAccuracy

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

def coefficientErrorVolumeLog {A : Type*} [Semiring A] (P : A) : A := P ^ 2 * (P + 61)

def coefficientErrorSpatialLog {A : Type*} [Semiring A] (P : A) : A :=
  P * (P ^ 3 + anisotropicSpatialCapLog P) + coefficientErrorVolumeLog P

theorem coefficientErrorSpatialLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coefficientErrorSpatialLog P := by
  have h := anisotropicSpatialCapLog_nonneg hP
  unfold coefficientErrorSpatialLog coefficientErrorVolumeLog
  positivity

theorem coefficientErrorPeriod_exp_sq {m M period : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ P) (hM : (M : ℝ) ≤ Real.exp P)
    (hperiod : period ≤ M ^ (m + 1)) : (period : ℝ) ≤ Real.exp (P ^ 2) := by
  have hcast : (period : ℝ) ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
  exact hcast.trans (by
    simpa only [pow_two] using pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hM hP (m + 1) hm)

theorem referenceErrorVolumeFactor_exp_bound (q : ℕ) (X : Type*) [Fintype X]
    {P D W L : ℝ} (hP : 0 ≤ P) (hq : ((q + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
        (((1 + W) / L) ^ q) ^ Fintype.card X ≤ Real.exp (coefficientErrorVolumeLog P) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hq' : (q : ℝ) + 1 ≤ P := by simpa only [Nat.cast_add, Nat.cast_one] using hq
  have hcount : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul hq' hX (Nat.cast_nonneg _) hP).trans_eq (pow_two P).symm
  have hprofile0 := smoothProbabilityProfile_pos_zero
  have hprofile : 30 / smoothProbabilityProfile 0 ≤ Real.exp 60 := by
    have hi := smoothProbabilityProfile_inner_lower 0 (by norm_num)
    apply le_trans (show 30 / smoothProbabilityProfile 0 ≤ 60 from
      (div_le_iff₀ hprofile0).mpr (by linarith))
    linarith [Real.add_one_le_exp (60 : ℝ)]
  have hprofilePower := pow_le_exp_mul_of_le_exp (by positivity) hprofile
    (by norm_num : (0 : ℝ) ≤ 60) _ hcount
  have hratio0 : 0 ≤ (1 + W) / L := by positivity
  have hratio : (1 + W) / L ≤ Real.exp (P + 1) := by
    apply (show (1 + W) / L ≤ 1 + D from (div_le_iff₀ hL0).mpr (by nlinarith)).trans
    exact one_add_le_exp_succ hP hD
  have hqPower := pow_le_exp_mul_of_le_exp hratio0 hratio (by positivity : 0 ≤ P + 1)
    q (by linarith : (q : ℝ) ≤ P)
  have hXPower := pow_le_exp_mul_of_le_exp (pow_nonneg hratio0 q) hqPower
    (by positivity : 0 ≤ P * (P + 1)) _ hX
  calc
    _ ≤ Real.exp (P ^ 2 * 60) * Real.exp (P * (P * (P + 1))) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold coefficientErrorVolumeLog; ring

theorem coarseReferenceMassConstant_exp_bound (q : ℕ) (X : Type*) [Fintype X]
    {P D W L : ℝ} (hP : 0 ≤ P) (hq : ((q + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    coarseReferenceMassConstant q X W L ≤ Real.exp (coefficientErrorVolumeLog P + 4) := by
  have h := referenceErrorVolumeFactor_exp_bound q X hP hq hX hL hW hD hWL
  have hprofile0 := smoothProbabilityProfile_pos_zero
  unfold coarseReferenceMassConstant
  rw [mul_assoc]
  calc
    _ ≤ Real.exp 4 * Real.exp (coefficientErrorVolumeLog P) := mul_le_mul
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) h (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem coefficientErrorSpatialFactor_exp_bound {G : Type*} [Fintype G] (q : ℕ)
    (X : Type*) [Fintype X] (selection : Fin q ↪ G) {M period : ℕ} {P D W L : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hq : ((q + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + W) / L) ^ q) ^ Fintype.card X
    0 ≤ Cψ * Vsp ∧ Cψ * Vsp ≤ Real.exp (coefficientErrorSpatialLog P) := by
  intro Cψ Vsp
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ P := by
    simpa [Nat.add_comm] using hq
  have hc := anisotropicSpatialDensityCap_exp_bound selection hP hM hMP hj hG
  have hc0 := anisotropicSpatialDensityCap_nonneg selection (by positivity : 0 ≤ 1 / (M : ℝ))
  have hh : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) ≤ Real.exp (P ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hperiod (sq_nonneg P) _ hj).trans_eq
      (congrArg Real.exp (by ring))
  have hb : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤
      Real.exp (P ^ 3 + anisotropicSpatialCapLog P) := by
    calc
      _ ≤ Real.exp (P ^ 3) * Real.exp (anisotropicSpatialCapLog P) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hcapLog := anisotropicSpatialCapLog_nonneg hP
  have hψ : Cψ ≤ Real.exp (P * (P ^ 3 + anisotropicSpatialCapLog P)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hb (by positivity) _ hX
  have hvol : Vsp ≤ Real.exp (coefficientErrorVolumeLog P) :=
    referenceErrorVolumeFactor_exp_bound q X hP hq hX hL hW hD hWL
  have hprofile0 := smoothProbabilityProfile_pos_zero
  refine ⟨by dsimp [Cψ, Vsp]; positivity, ?_⟩
  calc
    _ ≤ Real.exp (P * (P ^ 3 + anisotropicSpatialCapLog P)) *
        Real.exp (coefficientErrorVolumeLog P) := by gcongr
    _ = _ := by rw [← Real.exp_add]; rfl

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem spatialWindowFactor_le_referenceFactor (q : ℕ) (X : Type*) [Fintype X]
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin q)) * (((1 + W) / L) ^ q) ^ Fintype.card X ≤
      (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
        (((1 + W) / L) ^ q) ^ Fintype.card X := by
  have hb : (9 : ℝ) ≤ 30 / smoothProbabilityProfile 0 :=
    (le_div_iff₀ smoothProbabilityProfile_pos_zero).mpr (by
      nlinarith [(smoothProbabilityProfile_range 0).2])
  have hc : Fintype.card (X × (Unit ⊕ Fin q)) = Fintype.card (Option (Fin q) × X) := by
    simp [Nat.mul_comm, Nat.add_comm]
  rw [hc]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hb _) (by positivity)

theorem coefficientSquareSpatial_cost {G : Type*} [Fintype G] (q : ℕ)
    (X : Type*) [Fintype X] (selection : Fin q ↪ G) {M period : ℕ} {P D W L Q E : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hq : ((q + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) (hE0 : 0 ≤ E)
    (hE : E ≤ Real.exp (-(2 * Q + 2 * coefficientErrorSpatialLog P + 4))) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + W) / L) ^ q) ^ Fintype.card X
    let Wsp := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin q)) *
      (((1 + W) / L) ^ q) ^ Fintype.card X
    (Cψ * Wsp) * (Cψ * (Vsp * E)) ≤ (Real.exp (-Q) / 2) ^ 2 := by
  intro Cψ Vsp Wsp
  have hfactor := coefficientErrorSpatialFactor_exp_bound q X selection hP hM hMP hperiod
    hq hG hX hL hW hD hWL
  have hc : 0 ≤ Cψ := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (by positivity))) _
  have hw : Wsp ≤ Vsp := spatialWindowFactor_le_referenceFactor q X hW (lt_of_lt_of_le zero_lt_one hL)
  have hm : Cψ * Wsp ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (mul_le_mul_of_nonneg_left hw hc).trans hfactor.2
  have ht := sourceSquareAccuracy_cost (M := Cψ * Wsp) (C := 1) (V := Cψ * Vsp)
    (W := coefficientErrorSpatialLog P) (B := 0) (D := coefficientErrorSpatialLog P)
    zero_le_one hfactor.1 hE0 hm (by simp) hfactor.2
    (show E ≤ Real.exp (-(2 * Q + coefficientErrorSpatialLog P + 0 + coefficientErrorSpatialLog P + 4)) by
      convert hE using 1
      congr 1
      ring)
  simpa only [one_mul, mul_assoc] using ht

end Erdos3

end

end OAI
