import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialBudget
import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialData
import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorDimensionBudget
import OAI.Combinatorics.Progressions.Lattices.MajorTranslationIntegerEvaluation

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem majorTranslationDegreeReduced_twisted_integerEval
    {U : Type*} {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (x : U → ℤ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ
        (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) T
        (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA))) =
      T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ))
          (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (fun j => ((Sum.elim x β j : ℤ) : ℝ)) F) : ℂ) := by
  rw [majorTranslationPolynomialOrbit_integerEval,
    twistedBufferedTranslationPhase_majorSymbol M Ψ _ _ T A _ β hβ]
  have hcast : Sum.elim (fun j => (x j : ℝ)) (fun i => (β i : ℝ)) =
      (fun j => ((Sum.elim x β j : ℤ) : ℝ)) := by
    funext j
    cases j <;> rfl
  rw [hcast, fractionalCoefficientPolynomial_fourierChar]

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le)
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA)
            (D.raiseStepRealOrbit htd.le R.orbit) b ω hLayers) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_translation_major_twisted_correlation_step_drop d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass (fractionalCoefficientPolynomial F) ≤ B := by
    change realPolynomialMass (fractionalCoefficientPolynomial F) ≤
      (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hv : ∀ i : U ⊕ Fin m, 0 < Sum.elim (fun _ : U => 1) w i := by
      intro i
      cases i with
      | inl i => exact Nat.zero_lt_one
      | inr i => exact hw i
    have hh := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE F
      (Sum.elim (fun _ : U => 1) w) hv d hF
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  apply hstep w hw hwd M hM D htd Ψ
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) B K
    (majorZeroParameterSlice_degree w hw (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF))
    ((majorZeroParameterSlice_mass _).trans hmass) T hT hLip
    (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA)
    R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge
  convert hcorr using 1
  congr 1
  apply Finset.expect_congr rfl
  intro x hx
  rw [majorTranslationDegreeReduced_twisted_integerEval w d hw hwd M Ψ F hF A hA T x (β x) (hβ x hx)]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_potential
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C) := by
  obtain ⟨a, ha, hdetect⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop d hd
  obtain ⟨c, hc, hpotential⟩ := exists_translationMajorDetectedPotential d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajor_detected_potential_budget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  have hbudget₁ : p₁ ≤ (p + C)^C := (hbudget p hp).2
  have hbudget₂ : (p₁ + (p₁ + 2)^4 + 1 + c)^c ≤ (p + C)^C := (hbudget p hp).1
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hbudget₁).trans (hlarge i)
  obtain ⟨η, b, ω, hLayers, hη, _, hb, hfactor⟩ :=
    hdetect w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  obtain ⟨l, E, P, S, Vfast, V, q, hl, hlp, hprod, hE, hS, hfast, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd M hM (D.raiseStep htd.le) orbit partner b ω hLayers η hη
      (fun i => (lengths i : ℝ)) p₁ hp₁ hdim hbase hb hfactor
  have hexp₁ := Real.exp_le_exp.mpr hbudget₁
  have hexp₂ := Real.exp_le_exp.mpr hbudget₂
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hbudget₁,
    l, E, P, S, Vfast, V, q, hl, hlp.trans hexp₁, hprod, ?_, hS, ?_, hV,
    hderiv, hq, hqp.trans hexp₂, hgrid, hmass.trans hexp₂, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) (fun i => by exact_mod_cast hlengths i) hexp₁ E hE
  · convert hfast using 1
  · intro α
    exact ⟨(hcoeff α).1.trans hexp₂, (hcoeff α).2.trans hexp₂⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C) := by
  obtain ⟨a, ha, hdetect⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop d hd
  obtain ⟨c, hc, hpotential⟩ := exists_translationMajorDetectedPotentialData d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajor_detected_potential_budget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  have hbudget₁ : p₁ ≤ (p + C)^C := (hbudget p hp).2
  have hbudget₂ : (p₁ + (p₁ + 2)^4 + 1 + c)^c ≤ (p + C)^C := (hbudget p hp).1
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hbudget₁).trans (hlarge i)
  obtain ⟨η, b, ω, hLayers, hη, _, hb, hfactor⟩ :=
    hdetect w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  obtain ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd M hM (D.raiseStep htd.le) orbit partner b ω hLayers η hη
      (fun i => (lengths i : ℝ)) p₁ hp₁ hdim hbase hb hfactor
  have hexp₁ := Real.exp_le_exp.mpr hbudget₁
  have hexp₂ := Real.exp_le_exp.mpr hbudget₂
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hbudget₁, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp.trans hexp₁, hprod, ?_⟩
  refine ⟨?_, hS, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) (fun i => by exact_mod_cast hlengths i) hexp₁ E hE
  refine ⟨?_, hVfast, hv, ?_⟩
  · convert hfast using 1
  refine ⟨hW, ?_, ?_, hV, hderiv, ?_⟩
  · exact fun i j => (hh i j).trans hbudget₁
  · convert hP using 1
  refine ⟨hq, hqp.trans hexp₂, hgrid, hmass.trans hexp₂, ?_⟩
  intro α
  exact ⟨(hcoeff α).1.trans hexp₂, (hcoeff α).2.trans hexp₂⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem fractionalMajor_mem_weightedSupportLE {U : Type*} {m d : ℕ}
    (w : Fin m → ℕ) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (hF : F.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d) :
    fractionalCoefficientPolynomial F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous F
    (Sum.elim (fun _ : U => 1) w) d hF (mem_support_iff.mp hα)).le

theorem majorTranslationReduced_twisted_integerEval
    {U : Type*} {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (hF : F.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (x : U → ℤ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ
        (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) T
        (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalMajor_mem_weightedSupportLE w F hF) A hA))) =
      T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ))
          (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (fun j => ((Sum.elim x β j : ℤ) : ℝ)) F) : ℂ) := by
  exact majorTranslationDegreeReduced_twisted_integerEval w d hw hwd M Ψ F
    (fun _ hα => (hF (mem_support_iff.mp hα)).le) A hA T x β hβ

theorem exists_reduced_majorPolynomial_twisted_correlation_step_drop
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le)
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalMajor_mem_weightedSupportLE w F hF) A hA)
            (D.raiseStepRealOrbit htd.le R.orbit) b ω hLayers) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
  exact hstep w hw hwd M hM D htd Ψ F
    (fun _ hα => (hF (mem_support_iff.mp hα)).le) A hA K T hT hLip R p hp
    hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr

end Erdos3.PolynomialTranslationLie

end

end OAI
