import OAI.Combinatorics.Progressions.Estimates.ComplexUnitLocalLipschitz
import OAI.Combinatorics.Progressions.Geometry.WeightedTranslationBufferedCoordinates

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def translationDisplacementNN : ℝ≥0 :=
  ⟨weightedTranslationDisplacementConstant d m (Fintype.card (WeightedBasisIndex w d)),
    (weightedTranslationDisplacementConstant_pos _ _ _).le⟩

noncomputable def bufferedTranslationTermLip (Ψ : PatchKernel m) (M : ℝ≥0) : ℝ≥0 :=
  let C := translationDisplacementNN w d
  max (8 * C) ((Ψ.lip + ⟨2 * Real.pi, by positivity⟩ * (1 + M * m * d)) * C)

theorem bufferedTranslationTerm_lipschitz
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (β : Fin m → ℤ) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (bufferedTranslationTermLip w d Ψ M)
      (fun g => bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := translationDisplacementNN w d
  let L : ℝ≥0 := (Ψ.lip + ⟨2 * Real.pi, by positivity⟩ * (1 + M * m * d)) * C
  have hC : 0 < (C : ℝ) := weightedTranslationDisplacementConstant_pos _ _ _
  have heq : bufferedTranslationTermLip w d Ψ M = max (2 * (4 * C)) L := by
    dsimp [bufferedTranslationTermLip, L]
    congr 1
    ring
  rw [heq]
  apply lipschitzWith_of_complex_unit_near _ (4 * C) L
  · intro g
    simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
    exact Ψ.le_one _
  · intro x y hnear
    let z := x * y⁻¹
    have hz : z * y = x := by dsimp [z]; group
    have hdist : dist 1 z = dist x y := by
      have hh := (rightMetricSpace_isometry_mul_right
        ((weightedOrderedBasis w d hw).baseChange ℝ) y⁻¹).dist_eq y x
      simpa only [z, mul_inv_cancel, dist_comm y x] using hh
    have hsmall : (C : ℝ) * dist x y ≤ 1 / 4 := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat] at hnear
      linarith
    have hnearz : dist 1 z ≤ 1 / (C : ℝ) := by
      rw [hdist, le_div_iff₀ hC]
      nlinarith
    have hnearz' : dist 1 z ≤ 1 / weightedTranslationDisplacementConstant d m
        (Fintype.card (WeightedBasisIndex w d)) := hnearz
    have hb := bchRealTranslation_bounds_near_one w d hw hd hwd z
      (by simpa only [Fintype.card_fin] using hnearz')
    simp only [Fintype.card_fin] at hb
    change (∀ i, |(bchRealTranslationHom w d hwd z).base i| ≤ (C : ℝ) * dist 1 z) ∧
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        |eval a (bchRealTranslationHom w d hwd z).polynomial| ≤ (C : ℝ) * dist 1 z at hb
    rw [hdist] at hb
    have h := bufferedTranslationTerm_increment_bound Ψ D₀
      (bchRealTranslationHom w d hwd z) (bchRealTranslationHom w d hwd y) β
      (mul_nonneg hC.le dist_nonneg) hsmall hdegree hD hb.1 hb.2
    rw [← map_mul, hz] at h
    change _ ≤ ((Ψ.lip : ℝ) + 2 * Real.pi * (1 + (M : ℝ) * m * d)) *
      (C : ℝ) * dist x y
    simpa only [mul_assoc] using h

theorem bufferedTranslationPhase_lipschitz
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (2 * bufferedTranslationTermLip w d Ψ M)
      (fun g => bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd g)) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  exact separated_complex_tsum_lipschitz
    (fun β g => bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β)
    (fun β => bufferedTranslationTerm_lipschitz w d hw hd hwd Ψ D₀ M hdegree hD β)
    (fun g β γ => bufferedTranslationTerm_unique Ψ D₀ (bchRealTranslationHom w d hwd g) β γ)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

private theorem complex_mul_sub_mul_le_unit (a b c e : ℂ)
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * b - c * e‖ ≤ ‖a - c‖ + ‖b - e‖ := by
  rw [show a * b - c * e = (a - c) * b + c * (b - e) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  exact add_le_add
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (norm_nonneg (a - c)))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (b - e)))

namespace PolynomialTranslationLie

open MvPolynomial NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def twistedBufferedTranslationTermLip (Ψ : PatchKernel m) (A K : ℝ≥0) : ℝ≥0 :=
  max (2 * translationDisplacementNN w d)
    (bufferedTranslationTermLip w d Ψ A + K * translationDisplacementNN w d)

theorem twistedBufferedTranslationTerm_lipschitz (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (β : Fin m → ℤ) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (twistedBufferedTranslationTermLip w d Ψ A K)
      (fun g => twistedBufferedTranslationTerm M Ψ D₀ T (bchRealTranslationHom w d hwd g) β) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := translationDisplacementNN w d
  let B := bufferedTranslationTermLip w d Ψ A
  let ρ := bchRealTranslationHom w d hwd
  have hC : 0 < (C : ℝ) := weightedTranslationDisplacementConstant_pos _ _ _
  apply lipschitzWith_of_complex_unit_near _ C (B + K * C)
  · intro g
    exact twistedBufferedTranslationTerm_norm_le_one M Ψ D₀ T hT (ρ g) β
  · intro x y hnear
    let z := x * y⁻¹
    have hz : z * y = x := by dsimp [z]; group
    have hdist : dist 1 z = dist x y := by
      have hh := (rightMetricSpace_isometry_mul_right
        ((weightedOrderedBasis w d hw).baseChange ℝ) y⁻¹).dist_eq y x
      simpa only [z, mul_inv_cancel, dist_comm y x] using hh
    have hnearz : dist 1 z ≤ 1 / (C : ℝ) := by
      rw [hdist, le_div_iff₀ hC]
      simpa only [mul_comm] using hnear.le
    have hbounds := bchRealTranslation_bounds_near_one w d hw hd hwd z
    simp only [Fintype.card_fin] at hbounds
    have hb := (hbounds hnearz).1
    change ∀ i, |(ρ z).base i| ≤ (C : ℝ) * dist 1 z at hb
    rw [hdist] at hb
    let rx := fun i => (ρ x).base i - (β i : ℝ)
    let ry := fun i => (ρ y).base i - (β i : ℝ)
    have hres : dist rx ry ≤ (C : ℝ) * dist x y := by
      apply (dist_pi_le_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mpr
      intro i
      have hbase : (ρ x).base i = (ρ z).base i + (ρ y).base i := by
        rw [← hz, map_mul]
        rfl
      dsimp [rx, ry]
      rw [Real.dist_eq, hbase]
      rw [show (ρ z).base i + (ρ y).base i - (β i : ℝ) -
        ((ρ y).base i - (β i : ℝ)) = (ρ z).base i by ring]
      exact hb i
    have hmult : ‖T rx (fun i => (β i : ZMod M)) - T ry (fun i => (β i : ZMod M))‖ ≤
        (K : ℝ) * ((C : ℝ) * dist x y) := by
      simpa only [dist_eq_norm] using
        ((hLip (fun i => (β i : ZMod M))).dist_le_mul rx ry).trans
          (mul_le_mul_of_nonneg_left hres K.coe_nonneg)
    have hphase : ‖bufferedTranslationTerm Ψ D₀ (ρ x) β -
        bufferedTranslationTerm Ψ D₀ (ρ y) β‖ ≤ (B : ℝ) * dist x y := by
      simpa only [dist_eq_norm] using
        (bufferedTranslationTerm_lipschitz w d hw hd hwd Ψ D₀ A hdegree hD β).dist_le_mul x y
    have hbx : ‖bufferedTranslationTerm Ψ D₀ (ρ x) β‖ ≤ 1 := by
      simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
      exact Ψ.le_one _
    have hmul := complex_mul_sub_mul_le_unit
      (T rx (fun i => (β i : ZMod M))) (bufferedTranslationTerm Ψ D₀ (ρ x) β)
      (T ry (fun i => (β i : ZMod M))) (bufferedTranslationTerm Ψ D₀ (ρ y) β)
      hbx (hT _ _)
    apply hmul.trans
    apply (add_le_add hmult hphase).trans_eq
    simp only [NNReal.coe_add, NNReal.coe_mul]
    ring

theorem twistedBufferedTranslationPhase_lipschitz (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (2 * twistedBufferedTranslationTermLip w d Ψ A K)
      (fun g => twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd g)) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  exact separated_complex_tsum_lipschitz
    (fun β g => twistedBufferedTranslationTerm M Ψ D₀ T (bchRealTranslationHom w d hwd g) β)
    (fun β => twistedBufferedTranslationTerm_lipschitz w d hw hd hwd M Ψ D₀ A K
      hdegree hD T hT hLip β)
    (fun g β γ => twistedBufferedTranslationTerm_unique M Ψ D₀ T
      (bchRealTranslationHom w d hwd g) β γ)

end PolynomialTranslationLie

end Erdos3

end

end OAI
