import OAI.Combinatorics.Progressions.Dynamics.ReducedTwistedSelectionBudget
import OAI.Combinatorics.Progressions.Fourier.WeightedTranslationTwistedCentralFrequency
import OAI.Combinatorics.Progressions.Nilpotent.CanonicalReducedMajorTwistedNiltest

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_twisted_vertical_selection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [LieRing L] [LieAlgebra ℚ L]
      {m d t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M) (D : RationalFilteredNilmanifold L t e) (htd : t < d) (ω : U → ℕ)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (mass K : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ mass)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit ω)
      (R : D.Niltest ω) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ mass K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω (sample x) orbit)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest ω)
        (W : (D.raiseStep htd.le).Niltest ω),
        V.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        V.orbit = orbit ∧ V.normBound = 1 ∧
        W.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
          (raisedNiltestBudget p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((raisedNiltestBudget p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ m d t e w hw hd hwd _ _ _ _ _ _ _ _ _ M hM D htd ω Ψ D₀ mass K hdegree hD T hT hLip
    orbit R p hp hgeometry hbound hR hRcap B hB sample multiplier hmultiplier hcorr
  let Q := weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ mass K hdegree hD T hT hLip orbit
  have hQ : Q.ComplexityLE p :=
    weightedTranslationTwistedNiltest_complexity w d hw hwd M hM ω hd Ψ D₀ mass K hdegree hD T hT hLip orbit
      hgeometry hbound
  have hraise := le_raisedNiltestBudget p
  have hraisedcorr : Real.exp (-(raisedNiltestBudget p)) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hraise)).trans
    simpa only [Q, weightedTranslationTwistedNiltest_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hcorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget p) (hp.trans hraise)
      (hQ.mono hraise) (R.raiseStep_complexity htd.le hp hR)
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_twisted_selected_frequency_one w d hw hd hwd M hM Ψ D₀ T η V.observable
      hvertV hVne hpresV
  exact ⟨η, V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne, hbias⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_translation_major_twisted_vertical_selection (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [Fintype U] [LieRing L] [LieAlgebra ℚ L]
      {m t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M) (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ),
      (∀ x r, ‖T x r‖ ≤ 1) → (∀ r, LipschitzWith K (fun x => T x r)) →
      ∀ (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (Fintype.card U + m : ℕ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p → (K : ℝ) ≤ Real.exp p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ)
      (β : X → Fin m → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ∀ i, |eval (fun j => (sample x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        (T (fun i => eval (fun j => (sample x j : ℝ)) (A i) - (β x i : ℝ))
          (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (sample x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim (sample x) (β x) j : ℤ) : ℝ)) F) : ℂ)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1))
        (W : (D.raiseStep htd.le).Niltest (fun _ : U => 1)),
        V.ComplexityLE ((p + C) ^ C) ∧
        V.orbit = majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
          (fractionalMajorPolynomial_support w d F hF) A hA ∧ V.normBound = 1 ∧
        W.ComplexityLE ((p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤ (p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨a, ha, hdetector⟩ := exists_reducedMajorTranslationTwistedNiltest_complexity d
  obtain ⟨c, _, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  obtain ⟨C, hC, hbudget⟩ := exists_reducedTwistedSelectionBudget a c
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ _ m t e w hw hd hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hdim hMp hΨ hK hR hRcap B hB sample β multiplier hβ hmultiplier hcorr
  let Q := reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ F hF A hA K T hT hLip
  have hQ : Q.ComplexityLE ((p + a) ^ a) :=
    hdetector w hw hwd hd M hM Ψ F hF A hA K T hT hLip hp hdim hMp hΨ hK
  have hpq : p ≤ (p + a) ^ a := le_reducedTwistedInputBudget ha hp
  have hraise := le_raisedNiltestBudget ((p + a) ^ a)
  have hbasecorr : Real.exp (-p) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * R.eval (sample x)‖ := by
    convert hcorr using 1
    congr 1
    apply Finset.expect_congr rfl
    intro x hx
    rw [show Q.eval (sample x) = _ from
      reducedMajorTranslationTwistedNiltest_eval w d hw hwd hd M hM Ψ F hF A hA K T hT hLip
        (sample x) (β x) (hβ x hx)]
  have hraisedcorr : Real.exp (-(raisedNiltestBudget ((p + a) ^ a))) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg (hpq.trans hraise))).trans
    simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hbasecorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget ((p + a) ^ a)) (hp.trans (hpq.trans hraise))
      (hQ.mono hraise) (R.raiseStep_complexity htd.le (hp.trans hpq) (hR.mono hpq))
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_twisted_selected_frequency_one w d hw hd hwd M hM Ψ
      (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0)
      T η V.observable hvertV hVne hpresV
  have hcost := hbudget p hp
  exact ⟨η, V, W, hVc.mono hcost, hVo, hVn, hWc.mono hcost, hWo, hWn,
    fun i => (hVheight i).trans hcost, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne,
    (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hbias⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
