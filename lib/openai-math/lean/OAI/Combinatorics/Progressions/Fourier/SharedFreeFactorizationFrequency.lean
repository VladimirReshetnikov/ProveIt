import OAI.Combinatorics.Progressions.Linear.RankTwoOrbitTree
import OAI.Combinatorics.Progressions.Linear.SharedFreeCommonProjection

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.real_finite_refined_petal_vanish {J : Type*} [Fintype J]
    (hfreq : V.frequency = B.freeFrequency D) (d : J → Fin s)
    (a : FreeMagma J) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : J → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
    (i : J) (hi : i ∈ lieTreeSupport a)
    (hvi : v i ∈ fourPetalSpace ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
        ((D.dependentFreeSpan (d i)).baseChange ℝ)
        (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩))) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval v a) = 0 := by
  classical
  let e := Fintype.equivFin J
  have hweight : lieTreeWeight (fun k => (d (e.symm k)).val + 1) (FreeMagma.map e a) = s := by
    rw [lieTreeWeight_relabel]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hd
  have hsupp : e i ∈ lieTreeSupport (FreeMagma.map e a) := by
    rw [lieTreeSupport_relabel]
    exact ⟨i, hi, rfl⟩
  have h := B.real_correlation_refined_petal_vanish D E T hbQ hT V g hg D' hfreq
    (Fintype.card J) (fun k => d (e.symm k)) (FreeMagma.map e a) hweight
    ((lieTreeLength_relabel e a).trans hr) (fun k => v (e.symm k))
    (fun k => hv (e.symm k)) (e i) hsupp
    (by simpa only [Equiv.symm_apply_apply] using hvi)
  simpa only [lieTreeEval_relabel, Function.comp_def, Equiv.symm_apply_apply] using h

theorem CoefficientBases.real_refined_petal_add_invariant {J : Type*}
    (hfreq : V.frequency = B.freeFrequency D) (d : J → Fin s)
    (a : FreeMagma J) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (x y : J → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hx : ∀ i, x i ∈ (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
    (hy : ∀ i, y i ∈ fourPetalSpace ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
        ((D.dependentFreeSpan (d i)).baseChange ℝ)
        (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩))) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval (x + y) a) =
      realifyFunctional (B.freeFrequency D) (lieTreeEval x a) := by
  apply lieTree_eq_of_one_petal_vanish (realifyFunctional (B.freeFrequency D))
    (fun i => (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
    (fun i => fourPetalSpace ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
        ((D.dependentFreeSpan (d i)).baseChange ℝ)
        (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩)))
    (fun i => fourPetalSpace_le_first _ _) a _ x y hx hy
  intro v hv i hi
  exact B.real_finite_refined_petal_vanish D E T hbQ hT V g hg D' hfreq
    (fun k => d (lieTreeOccurrenceLabel a k)) (lieTreeOccurrenceTree a)
    ((lieTreeOccurrenceTree_weight (fun k => (d k).val + 1) a).trans hd)
    ((lieTreeOccurrenceTree_length a).trans hr) v hv i
    (by rw [lieTreeOccurrenceTree_support]; trivial) hi

theorem CoefficientBases.real_corrected_common_petal_invariant {J : Type*}
    (hfreq : V.frequency = B.freeFrequency D)
    (γ : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hγ : ∀ d, γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (u p : J → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hu : ∀ i, u i ∈ (D.dependentFreeSpan (d i)).baseChange ℝ)
    (hp : ∀ i, p i ∈ (fourPetalSpace (D.dependentFreeSpan (d i))
      (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
        (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩))).baseChange ℝ) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval (fun i => γ (d i) + u i + p i) a) =
      realifyFunctional (B.freeFrequency D) (lieTreeEval (fun i => γ (d i) + u i) a) := by
  have hspace (k : Fin s) := realification_fourRefinedRelation (D.coefficientFreeSpan k)
    (D.dependentFreeSpan k) (D'.coefficientFourSpace ⟨k.val + 1, by omega⟩)
  have hfirst (k : Fin s) := realification_firstProjection
    (fourRefinedRelation (D.coefficientFreeSpan k) (D.dependentFreeSpan k)
      (D'.coefficientFourSpace ⟨k.val + 1, by omega⟩))
  have hpetal (k : Fin s) := realification_fourPetalSpace (D.dependentFreeSpan k)
    (fourRefinedRelation (D.coefficientFreeSpan k) (D.dependentFreeSpan k)
      (D'.coefficientFourSpace ⟨k.val + 1, by omega⟩))
  simp_rw [hspace] at hfirst hpetal
  apply B.real_refined_petal_add_invariant D E T hbQ hT V g hg D' hfreq d a hd hr
    (fun i => γ (d i) + u i) p
  · intro i
    have h₁ := hγ (d i)
    have h₂ := Submodule.baseChange_mono ℝ
      (dependent_le_refined_firstProjection (D.coefficientFreeSpan (d i))
        (D.dependentFreeSpan (d i)) (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)) (hu i)
    rw [hfirst] at h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  · intro i
    have h := hp i
    rw [hpetal] at h
    exact h

theorem CoefficientBases.exists_corrected_common_petal_invariance
    (F : FreeCoordinateFrame E.basis Q) (hfreq : V.frequency = B.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, VectorPolynomial.coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), VectorPolynomial.coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      (∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        VectorPolynomial.coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d)) ∧
      ∀ (n : ℕ) (d : Fin n → Fin s) (a : FreeMagma (Fin n)),
        lieTreeWeight (fun i => (d i).val + 1) a = s → a.length = r →
        ∀ u p : Fin n → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
          (∀ i, u i ∈ (D.dependentFreeSpan (d i)).baseChange ℝ) →
          (∀ i, p i ∈ (fourPetalSpace (D.dependentFreeSpan (d i))
            (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
              (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩))).baseChange ℝ) →
          realifyFunctional (B.freeFrequency D) (lieTreeEval (fun i => γ (d i) + u i + p i) a) =
            realifyFunctional (B.freeFrequency D) (lieTreeEval (fun i => γ (d i) + u i) a) := by
  intro Λ
  obtain ⟨m, γ, e, q, hcommon⟩ := D.exists_shared_free_common_projection E T hbQ hT F V g hg D'
    hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  refine ⟨m, γ, e, q, hcommon, ?_⟩
  intro n d a hd hr u p hu hp
  exact B.real_corrected_common_petal_invariant D E T hbQ hT V g hg D' hfreq γ
    (fun d => (hcommon d).2.2.1) d a hd hr u p hu hp

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.real_corrected_orbit_petal_invariant {I : Type*}
    (hs : 1 ≤ s) (hfreq : V.frequency = B.freeFrequency D)
    (γ v : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hγ : ∀ d, γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hv : ∀ d, v d ∈ (D.dependentFreeSpan d).baseChange ℝ)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA : ∀ d, coefficients A.log (Finsupp.single () (d.val + 1)) = γ d + v d)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
    (d : I → Fin s) (a : FreeMagma I)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r) :
    realifyFunctional (B.freeFrequency D)
      (lieTreeEval (fun i => coefficients (A * K * U).log (Finsupp.single () ((d i).val + 1))) a) =
    realifyFunctional (B.freeFrequency D)
      (lieTreeEval (fun i => coefficients A.log (Finsupp.single () ((d i).val + 1))) a) := by
  rw [T.top_tree_product_rank_two hs A K U hK d a hd hr]
  simp_rw [hA]
  exact B.real_corrected_common_petal_invariant D E T hbQ hT V g hg D' hfreq γ hγ d a hd hr
    (fun i => v (d i)) (fun i => coefficients U.log (Finsupp.single () ((d i).val + 1)))
    (fun i => hv (d i)) (fun i => hU (d i))

theorem CoefficientBases.real_affine_orbit_petal_invariant {I : Type*} {n : ℕ}
    (hs : 1 ≤ s) (hfreq : V.frequency = B.freeFrequency D)
    (Γ A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (β : Fin n → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) (x : Fin n → ℤ)
    (hΓ : ∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hα : ∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ)
    (hβ : ∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ)
    (hA : A.log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d))
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
    (d : I → Fin s) (a : FreeMagma I)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r) :
    realifyFunctional (B.freeFrequency D)
      (lieTreeEval (fun i => coefficients (A * K * U).log (Finsupp.single () ((d i).val + 1))) a) =
    realifyFunctional (B.freeFrequency D)
      (lieTreeEval (fun i => coefficients A.log (Finsupp.single () ((d i).val + 1))) a) := by
  apply B.real_corrected_orbit_petal_invariant D E T hbQ hT V g hg D' hs hfreq
    (fun j => coefficients Γ.log (Finsupp.single () (j.val + 1)))
    (fun j => α j + ∑ k, (x k : ℝ) • β k j) hΓ _ A K U _ hK hU d a hd hr
  · intro j
    exact Submodule.add_mem _ (hα j)
      (Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hβ k j)))
  · intro j
    rw [hA, map_add, Finsupp.add_apply, positiveUnivariate_coefficient]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
