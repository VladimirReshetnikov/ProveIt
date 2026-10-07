import OAI.Combinatorics.Progressions.Dynamics.SharedFreeLowerComparisonBudget

namespace OAI

section

namespace Erdos3

noncomputable def nativeLowerPairModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  ((p + nativePairModelConstant s) ^ nativePairModelConstant s + rankUnitDescentConstant s) ^
    rankUnitDescentConstant s

theorem exists_nativeLowerPairModelBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
      nativeLowerPairModelBudget s p ≤ (p + C) ^ C := by
  let a := nativePairModelConstant s
  let b := rankUnitDescentConstant s
  let A : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A + (A + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C := by
    simpa [A, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨(le_add_of_nonneg_right hb).trans hsum, (le_add_of_nonneg_left ha).trans hsum⟩

end Erdos3

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_uniform_lower_pair_model {L I : Type} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure (r + 1))
    (S : Fin s → Submodule ℚ (Fin 2 → L))
    (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
    (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
    {p : ℝ} (hp : 2 ≤ p) (hT : T.ComplexityLE p)
    (hB : ∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => D.basis)).repr
      (B j a : Fin 2 → L) i) ≤ p)
    (V : D.UnitVerticalObservable (T.realSubgroup s (r + 1)) I p)
    (hzero : ∀ x ∈ (filtration S T.filtration.rank_le_degree).layer s (r + 1),
      pairDifferenceFunctional V.frequency
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS x) = 0) :
    let pM := (p + nativePairModelConstant s) ^ nativePairModelConstant s
    let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
    ∃ M : RationalFilteredNilmanifold (Algebra S (r + 1)) s (finrank ℚ (Algebra S (r + 1))),
      ∃ U : M.DegreeRankStructure (r + 1),
        U.filtration = filtration S T.filtration.rank_le_degree ∧ U.ComplexityLE pM ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S (r + 1))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S (r + 1)) :=
           IsModuleTopology.isTopologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 M.basis
         ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1)) (I × I) pM,
           (∀ i x, Z.observable i (QuotientGroup.mk x) =
             V.pairedObservable T i (QuotientGroup.mk (realificationMap
               (hnil := M.filtration.lowerCentralSeries_eq_bot)
               (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
           M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
             (nativeLowerPairModelBudget s p)) := by
  intro pM φ
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fin 2 → L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (Pi.basis (fun _ : Fin 2 => D.basis))
  obtain ⟨M, U, hU, hUc, _, _, _, _, hZ⟩ :=
    (exists_native_pair_model.{0, 0} s).choose_spec.2 L I (r + 1) d D T S B hS p hp hT hB V
  refine ⟨M, U, hU, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S (r + 1)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hfreq, hobs⟩ := hZ
  refine ⟨Z, hobs, ?_⟩
  have hZzero : ∀ x ∈ U.filtration.layer s (r + 1), Z.frequency x = 0 := by
    intro x hx
    rw [hfreq]
    exact hzero x (by simpa only [hU] using hx)
  exact UnitVerticalObservable.hasUniformLowerRankUnitFamily M U Z (fun _ : Unit => 1)
    ((Nat.cast_nonneg _).trans hUc.1.1) hUc hZzero

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_covered_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (Λ : Subgroup E.filtration.Group) (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
    (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m)
    {p₁ : ℝ} (hp₁ : 0 ≤ p₁) (hT₁ : (T.withLattice Λ m hm hin hout).ComplexityLE p₁)
    (V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁)
    (hV₁ : V₁.frequency = V.frequency) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    let E₁ := E.withLattice Λ m hm hin hout
    let T₁ := T.withLattice Λ m hm hin hout
    let pM := (q₁ + nativePairModelConstant s) ^ nativePairModelConstant s
    ∃ J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (J j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S J (piRank (fun _ : Fin 2 => E₁) (fun _ => T₁)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
          (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
        ∃ U : M.DegreeRankStructure (r + 1),
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE pM ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
             IsModuleTopology.isTopologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
               (Fin W.family.outputDim × Fin W.family.outputDim) pM,
             (∀ i x, Z.observable i (QuotientGroup.mk x) =
               V₁.pairedObservable T₁ i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E₁)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
             M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
               (nativeLowerPairModelBudget s q₁)) := by
  intro S hS q₁ E₁ T₁ pM
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := sharedFreeComparisonBasisBudget_nonneg hQ hP'
  have hq : 2 ≤ q₁ := by dsimp only [q₁]; linarith
  have hpq : p₁ ≤ q₁ := by dsimp only [q₁]; linarith
  have hBq : sharedFreeComparisonBasisBudget Q P' ≤ q₁ := by dsimp only [q₁]; linarith
  obtain ⟨J, hJ⟩ := D.exists_comparisonCoefficientBases E T hbQ hT F V g hg D'
    hTfil hs hP' hQP'
  refine ⟨J, hJ, ?_⟩
  apply SubspaceFreeLift.exists_uniform_lower_pair_model E₁ T₁ S J hS hq
    (hT₁.mono T₁ hpq) (fun j a i => (hJ j a i).trans hBq) (V₁.mono hpq)
  intro x hx
  change pairDifferenceFunctional V₁.frequency
    (SubspaceFreeLift.evaluation S J (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS x) = 0
  rw [hV₁]
  exact B₀.comparison_free_top_frequency D E T hbQ hT V g hg D' hTfil hfreq J x hx

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_covered_factored_family {τ : Type*}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (Λ : Subgroup E.filtration.Group) (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
    (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m)
    {p₁ : ℝ} (hp₁ : 0 ≤ p₁) (hT₁ : (T.withLattice Λ m hm hin hout).ComplexityLE p₁)
    (V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁)
    (hV₁ : V₁.frequency = V.frequency)
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t (d : Fin s), coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t (d : Fin s), coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t (d : Fin s), coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
      ∃ Tm : M.DegreeRankStructure (r + 1),
        Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
        Tm.ComplexityLE ((q₁ + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
        M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
          (fun t (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
            V₁.observable i.1 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t * K t * U t))) *
            star (V₁.observable i.2 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t)))))
          (nativeLowerPairModelBudget s q₁) := by
  intro S q₁
  let E₁ := E.withLattice Λ m hm hin hout
  let T₁ := T.withLattice Λ m hm hin hout
  obtain ⟨J, _, M, Tm, hTm, hTmc, hZ⟩ :=
    B₀.exists_covered_comparison D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Λ m hm hin hout hp₁ hT₁ V₁ hV₁
  refine ⟨M, Tm, hTm, hTmc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hobs, huniform⟩ := hZ
  apply huniform.realizeFamily
  intro t
  obtain ⟨u, hu0, _, hu⟩ := D.exists_native_factored_comparison_orbit E T hbQ hT V g hg D'
    hTfil (by omega) (A t) (K t) (U t) (hA0 t) (hK0 t) (hU0 t) (hA t) (hK t) (hU t)
    J M Tm hTm
  refine ⟨u, hu0, ?_⟩
  intro i x
  exact SubspaceFreeLift.native_pair_observable_eval E₁ T₁ S J
    (D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil)
    M Tm V₁ Z hobs ![A t * K t * U t, A t] u hu i x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreeFrozenCoverBudget (s : ℕ) (p : ℝ) : ℝ :=
  (p + (RationalFilteredNilmanifold.exists_shared_frozen_unit_observable.{0, 0, 0} s 1).choose) ^
    (RationalFilteredNilmanifold.exists_shared_frozen_unit_observable.{0, 0, 0} s 1).choose

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_frozen_comparison {τ : Type}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hf : ∀ x, ‖f x‖ ≤ 1)
    {pF ε : ℝ} (hpF : 0 ≤ pF) (hQF : Q ≤ pF) (hε : 0 < ε) (hεF : 1 / ε ≤ Real.exp pF)
    (q₀ : ℕ) (hq₀ : 0 < q₀) (hqF : (q₀ : ℝ) ≤ Real.exp pF)
    (J₀ : Finset τ) (hJ₀ : J₀.Nonempty) (a u : τ → E.RealGroup)
    (ha : ∀ t ∈ J₀, ∀ i, |(E.basis.baseChange ℝ).repr (a t).coord i| ≤ Real.exp ((pF + 2) ^ 1))
    (hu : ∀ t ∈ J₀, ∀ i, |(E.basis.baseChange ℝ).repr (u t).coord i| ≤ Real.exp ((pF + 2) ^ 1))
    (hugrid : ∀ t ∈ J₀, (E.basis.baseChange ℝ).equivFun (u t).coord ∈ realDenominatorGrid q₀)
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t ∈ J₀, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t ∈ J₀, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t ∈ J₀, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t ∈ J₀, ∀ d : Fin s, coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t ∈ J₀, ∀ d : Fin s, coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t ∈ J₀, ∀ d : Fin s, coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let p₁ := sharedFreeFrozenCoverBudget s pF
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ Λ : Subgroup E.filtration.Group, Λ ≤ E.lattice ∧
      (Λ.subgroupOf E.lattice).Characteristic ∧ (Λ.subgroupOf E.lattice).Normal ∧
      (Λ.subgroupOf E.lattice).FiniteIndex ∧ (Λ.relIndex E.lattice : ℝ) ≤ Real.exp p₁ ∧
      ∃ (m : ℕ) (hm : 0 < m)
        (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
        (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m),
        (T.withLattice Λ m hm hin hout).ComplexityLE p₁ ∧
        ∃ J : Finset τ, J ⊆ J₀ ∧ J.Nonempty ∧ Real.exp (-p₁) * J₀.card ≤ (J.card : ℝ) ∧
        ∃ V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
            ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁,
          V₁.frequency = V.frequency ∧
          (∀ t ∈ J, ∀ i (b c : E.RealGroup),
            ‖V.observable i (QuotientGroup.mk (a t * b * u t)) -
              ∑ j, (V₁.observable i (QuotientGroup.mk b) *
                star (V₁.observable j (QuotientGroup.mk c))) *
                V₁.observable j (QuotientGroup.mk c)‖ ≤ (V.lipBound : ℝ) * ε) ∧
          (∀ t ∈ J, ∀ (h : ZMod N) (v : ZMod N → E.RealGroup) (pC : ℝ),
            (V.lipBound : ℝ) * ε ≤ Real.exp (-(2 * pC)) / 2 →
            Nonempty (NativeVectorCorrelation (s - 1) N pC
              (W.replacedRankResidual h (fun i x => V.observable i
                (QuotientGroup.mk (a t * v x * u t))))) →
            Nonempty (NativeVectorCorrelation (s - 1) N (pC + 1)
              (W.replacedRankResidual h (fun i x => V₁.observable i
                (QuotientGroup.mk (v x)))))) ∧
          ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
              (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
            ∃ Tm : M.DegreeRankStructure (r + 1),
              Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
              Tm.ComplexityLE ((q₁ + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
              M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                (fun (t : {t // t ∈ J}) (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
                  V₁.observable i.1 (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x
                      (A t.val * K t.val * U t.val))) *
                  star (V₁.observable i.2 (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t.val)))))
                (nativeLowerPairModelBudget s q₁) := by
  intro p₁ q₁ S
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hT₁, J, hsub, hJ, hdense, V₁, hV₁, happ⟩ :=
    (RationalFilteredNilmanifold.exists_shared_frozen_unit_observable.{0, 0, 0} s 1).choose_spec.2
      E T hpF (hT.mono T hQF) hε hεF q₀ hq₀ hqF (V.mono hQF) J₀ a u hJ₀ ha hu hugrid
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
    hT₁, J, hsub, hJ, hdense, V₁, hV₁, ?_, ?_, ?_⟩
  · intro t ht i b c
    rw [← complex_unit_vector_resolution (fun j => V₁.observable j (QuotientGroup.mk c))
      (V₁.unit (QuotientGroup.mk c)) (V₁.observable i (QuotientGroup.mk b))]
    exact happ t ht i b
  · intro t ht h v pC hsmall hcorr
    obtain ⟨C⟩ := hcorr
    apply C.exists_of_uniform_approx
    intro ij x
    exact (W.replacedRankResidual_norm_sub_le hf h _ _ ij x).trans
      ((happ t ht ij.2 (v x)).trans hsmall)
  · exact B₀.exists_covered_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Λ m hm hin hout ((Nat.cast_nonneg _).trans hT₁.1.1) hT₁ V₁ hV₁
      (fun t : {t // t ∈ J} => A t.val) (fun t : {t // t ∈ J} => K t.val)
      (fun t : {t // t ∈ J} => U t.val)
      (fun t => hA0 t.val (hsub t.property)) (fun t => hK0 t.val (hsub t.property))
      (fun t => hU0 t.val (hsub t.property)) (fun t => hA t.val (hsub t.property))
      (fun t => hK t.val (hsub t.property)) (fun t => hU t.val (hsub t.property))

end Erdos3.NativeRankRelation.CommonData

end

end OAI
