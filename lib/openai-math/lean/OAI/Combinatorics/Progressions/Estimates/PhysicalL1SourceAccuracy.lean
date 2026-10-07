import OAI.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget

namespace OAI

section

namespace Erdos3

noncomputable def l1SourceAccuracy (target spatialCap spatialVolume : ℝ) : ℝ :=
  Real.exp (-(target + spatialCap + spatialVolume + 8))

theorem l1SourceAccuracy_pos (target spatialCap spatialVolume : ℝ) :
    0 < l1SourceAccuracy target spatialCap spatialVolume := Real.exp_pos _

theorem l1SourceAccuracy_inv (target spatialCap spatialVolume : ℝ) :
    (l1SourceAccuracy target spatialCap spatialVolume)⁻¹ =
      Real.exp (target + spatialCap + spatialVolume + 8) := by
  unfold l1SourceAccuracy
  rw [← Real.exp_neg, neg_neg]

theorem l1Source_error_le_exp
    {target spatialCap spatialVolume Cψ factor window E δ η ε εtrunc : ℝ}
    (hC0 : 0 ≤ Cψ) (hC : Cψ ≤ Real.exp spatialCap)
    (hf0 : 0 ≤ factor) (hf : factor ≤ Real.exp spatialVolume)
    (hw0 : 0 ≤ window) (hw : window ≤ Real.exp spatialVolume)
    (hE : E ≤ l1SourceAccuracy target spatialCap spatialVolume)
    (hδ : δ ≤ l1SourceAccuracy target spatialCap spatialVolume)
    (hη : η ≤ l1SourceAccuracy target spatialCap spatialVolume)
    (hε : ε ≤ l1SourceAccuracy target spatialCap spatialVolume)
    (ht : εtrunc ≤ l1SourceAccuracy target spatialCap spatialVolume) :
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  let e := l1SourceAccuracy target spatialCap spatialVolume
  have he : 0 ≤ e := (l1SourceAccuracy_pos _ _ _).le
  have hsum : E + 2 * δ + (2 * η + ε) ≤ 6 * e := by dsimp only [e]; linarith
  have hfirst : factor * (E + 2 * δ + (2 * η + ε)) ≤ Real.exp spatialVolume * (6 * e) :=
    (mul_le_mul_of_nonneg_left hsum hf0).trans (mul_le_mul_of_nonneg_right hf (by positivity))
  have hsecond : window * εtrunc ≤ Real.exp spatialVolume * e :=
    (mul_le_mul_of_nonneg_left ht hw0).trans (mul_le_mul_of_nonneg_right hw he)
  have hb : factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc ≤
      7 * Real.exp spatialVolume * e := by linarith
  have h7 : (7 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ Real.exp spatialCap * (7 * Real.exp spatialVolume * e) :=
      (mul_le_mul_of_nonneg_left hb hC0).trans (mul_le_mul_of_nonneg_right hC (by positivity))
    _ ≤ Real.exp spatialCap * (Real.exp 8 * Real.exp spatialVolume * e) := by gcongr
    _ = _ := by
      dsimp only [e, l1SourceAccuracy]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem l1Source_error_le_exp_of_joint_bound
    {target budget Cψ factor window E δ η ε εtrunc : ℝ}
    (hC0 : 0 ≤ Cψ) (hf0 : 0 ≤ factor) (hw0 : 0 ≤ window)
    (hf : Cψ * factor ≤ Real.exp budget) (hw : Cψ * window ≤ Real.exp budget)
    (hE : E ≤ l1SourceAccuracy target budget 0)
    (hδ : δ ≤ l1SourceAccuracy target budget 0)
    (hη : η ≤ l1SourceAccuracy target budget 0)
    (hε : ε ≤ l1SourceAccuracy target budget 0)
    (ht : εtrunc ≤ l1SourceAccuracy target budget 0) :
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  let e := l1SourceAccuracy target budget 0
  have he : 0 ≤ e := (l1SourceAccuracy_pos _ _ _).le
  have hsum : E + 2 * δ + (2 * η + ε) ≤ 6 * e := by dsimp only [e]; linarith
  have hfirst : (Cψ * factor) * (E + 2 * δ + (2 * η + ε)) ≤ Real.exp budget * (6 * e) :=
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hf0)).trans
      (mul_le_mul_of_nonneg_right hf (by positivity))
  have hsecond : (Cψ * window) * εtrunc ≤ Real.exp budget * e :=
    (mul_le_mul_of_nonneg_left ht (mul_nonneg hC0 hw0)).trans (mul_le_mul_of_nonneg_right hw he)
  have h7 : (7 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 7 * Real.exp budget * e := by nlinarith only [hfirst, hsecond]
    _ ≤ Real.exp 8 * Real.exp budget * e := by gcongr
    _ = _ := by
      dsimp only [e, l1SourceAccuracy]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem physicalWindowFactor_le_referenceFactor (dim : ℕ) (X : Type*) [Fintype X]
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X ≤
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hc : Fintype.card (X × (Unit ⊕ Fin dim)) = Fintype.card (Option (Fin dim) × X) := by
    simp [Nat.add_comm, Nat.mul_comm]
  rw [hc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9)
  apply (le_div_iff₀ smoothProbabilityProfile_pos_zero).mpr
  linarith [(smoothProbabilityProfile_range 0).2]

theorem physicalL1Source_error_le_exp {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    {E δ η ε εtrunc : ℝ}
    (hE : E ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hδ : δ ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hη : η ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hε : ε ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (ht : εtrunc ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  intro Cψ factor window
  have hC : 0 ≤ Cψ := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg _)))) _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hratio : 0 ≤ (1 + W) / L := div_nonneg (by linarith) hL0.le
  have hf0 : 0 ≤ factor := mul_nonneg (pow_nonneg (div_nonneg (by norm_num)
    smoothProbabilityProfile_pos_zero.le) _) (pow_nonneg (pow_nonneg hratio _) _)
  have hw0 : 0 ≤ window := mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (pow_nonneg hratio _) _)
  have hf := (coefficientErrorSpatialFactor_exp_bound dim X selection hP hM hMP hperiod
    hdim hG hX hL hW hD hWL).2
  have hw : Cψ * window ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (mul_le_mul_of_nonneg_left (physicalWindowFactor_le_referenceFactor dim X hW hL0) hC).trans hf
  exact l1Source_error_le_exp_of_joint_bound hC hf0 hw0 hf hw hE hδ hη hε ht

theorem physicalL1Source_error_le_exp_of_precision {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target precision : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hprecision : target + coefficientErrorSpatialLog P + 8 ≤ precision)
    {η ε εtrunc : ℝ}
    (hη : η ≤ Real.exp (-precision)) (hε : ε ≤ Real.exp (-precision))
    (ht : εtrunc ≤ Real.exp (-precision)) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (Real.exp (-precision) + 2 * Real.exp (-precision) + (2 * η + ε)) +
      window * εtrunc) ≤ Real.exp (-target) := by
  have ha : Real.exp (-precision) ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0 := by
    unfold l1SourceAccuracy
    apply Real.exp_le_exp.mpr
    linarith
  exact physicalL1Source_error_le_exp dim X selection hP hM hMP hperiod hdim hG hX hL hW hD hWL
    ha ha (hη.trans ha) (hε.trans ha) (ht.trans ha)

end Erdos3

end

end OAI
