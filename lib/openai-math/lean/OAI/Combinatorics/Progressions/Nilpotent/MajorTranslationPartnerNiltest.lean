/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.MajorTranslationPartnerBudget
import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module RationalFilteredNilmanifold
open scoped NNReal TensorProduct

noncomputable abbrev majorTranslationPartnerModel {L : Type}
    [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
    (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)]
    (D : RationalFilteredNilmanifold L t e) (htd : t ≤ d) :=
  pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd))

theorem exists_majorTranslation_partner_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [LieRing L] [LieAlgebra ℚ L]
      {m t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t ≤ d)
      (R : D.Niltest (fun _ : U => 1)) (_hd : 0 < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (_hA : ∀ i, (A i).totalDegree ≤ w i)
      (p : ℝ), 0 ≤ p → (Fintype.card U + m : ℕ) ≤ p →
      (Ψ.lip : ℝ) ≤ Real.exp p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      let N := majorTranslationPartnerModel w d hw hwd D htd
      letI : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
        N.basis.finiteDimensional_of_finite
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
        realification_moduleTopology_t2 N.basis
      ∃ S : N.Niltest (fun _ : U => 1), S.normBound = 1 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          S.eval u =
            ((Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) F) : ℂ)) *
                R.eval u := by
  obtain ⟨a, ha, hmajor⟩ := exists_majorTranslation_degree_reduced_niltest d
  obtain ⟨C, hC, hbudget⟩ := exists_majorTranslationPartnerBudget_bound a
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd R hd Ψ F hF A hA p
    hp hdim hΨ hR hcap
  let N := majorTranslationPartnerModel w d hw hwd D htd
  let : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
    N.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    realification_moduleTopology_t2 N.basis
  obtain ⟨V, hVnorm, hV, _, hVeval⟩ := hmajor w hw hwd hd Ψ F hF A hA hp hdim hΨ
  let q : ℝ := (p + a) ^ a + raisedNiltestBudget p + 2
  have hraise : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hVq : V.ComplexityLE q := hV.mono (by dsimp [q]; linarith)
  have hRq : (R.raiseStep htd).ComplexityLE q :=
    (R.raiseStep_complexity htd hp hR).mono (by dsimp [q]; linarith)
  let models := pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd)
  let tests := pairTests (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd)
    V (R.raiseStep htd)
  have htests : ∀ i, (tests i).ComplexityLE q :=
    pairTests_complexity _ _ V (R.raiseStep htd) hVq hRq
  have hcaps : ∀ i, (tests i).normBound ≤ 1 := by
    intro i
    cases i
    · change R.normBound ≤ 1
      exact_mod_cast hcap
    · change V.normBound ≤ 1
      exact hVnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ q := by simpa using hq
  let S := unitBoundedPiNiltest models tests (by linarith : 0 ≤ q) hcard htests hcaps
  refine ⟨S, rfl, ?_, ?_⟩
  · exact (unitBoundedPiNiltest_complexity models tests (by linarith : 0 ≤ q)
      hcard htests hcaps).mono (hbudget p hp)
  · intro u β hβ
    change (unitBoundedPiNiltest models tests _ _ _ _).eval u = _
    rw [unitBoundedPiNiltest_eval, Fintype.prod_bool]
    change V.eval u * (R.raiseStep htd).eval u = _
    rw [hVeval u β hβ, R.raiseStep_eval]

end Erdos3.PolynomialTranslationLie

end

end OAI
