import OAI.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem dependent_le_refined_firstProjection
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    D ≤ (fourRefinedRelation C D K).map (LinearMap.proj 0) := by
  intro v hv
  refine ⟨fun _ : Fin 4 => v, fourBalancedDependent_le_refined C D K ?_, rfl⟩
  exact (mem_fourBalancedDependent D _).mpr ⟨fun _ => hv, by abel⟩

theorem realification_firstProjection
    {V : Type*} [AddCommGroup V] [Module ℚ V] (K : Submodule ℚ (Fin 4 → V)) :
    (K.map (LinearMap.proj 0)).baseChange ℝ =
      ((K.baseChange ℝ).map (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap).map
        (LinearMap.proj 0) := by
  rw [realification_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, (real_four_projection y 0).symm⟩
  · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, real_four_projection y 0⟩

theorem real_four_projection_norm_le
    {V ι : Type*} [LieRing V] [LieAlgebra ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) :
    ‖(b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x)‖ ≤
      ‖((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) i| ≤ _
  rw [real_pi_projection_coordinates]
  exact norm_le_pi_norm (((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x) ⟨k, i⟩

theorem real_four_projection_grid
    {V ι : Type*} [LieRing V] [LieAlgebra ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) (l : ℕ)
    (hx : ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => z ⟨k, i⟩, funext fun i => ?_⟩
  exact (congrFun hz ⟨k, i⟩).trans (congrArg (fun a : ℝ => (l : ℝ) * a)
    (real_pi_projection_coordinates b x k i).symm)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
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
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
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

include F

theorem exists_shared_free_common_projection
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      ∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d) := by
  intro Λ
  classical
  let z := 8 * sharedRefinementInputBudget s P' + 1
  let A₀ := sharedFreeEquationInputBudget s Q P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hbudget := (sharedFreeAffineConstant_spec s).2 Q P' hQ hQP' hP' 0
    (by simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg s)) hP')
  have hcut := sharedFreeRecoveryThreshold_spec s hQ hP' N
    ((Real.exp_le_exp.mpr hbudget.1).trans hN)
  have hb := sharedFreeEquationInputBudget_bounds s hQ hP'
  have hA₀ : 0 ≤ A₀ := hb.1
  have hcoeff := sharedFreeRecoveryThreshold_coefficient_bounds s hQ hP'
  have hAΛ : A₀ ≤ Λ :=
    (le_power_budget hb.1 (by decide : 1 ≤ 4)).trans (hcoeff.1.trans hbudget.1)
  have hnum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤ Real.exp Λ := by
    have hfac : 1 ≤ 2 * Real.exp ((A₀ + 2) ^ 3) := by
      have h := Real.one_le_exp_iff.mpr (show 0 ≤ (A₀ + 2) ^ 3 by positivity)
      linarith
    calc
      _ ≤ 2 * (Real.exp ((A₀ + 2) ^ 3) *
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) := by
        have h := mul_le_mul_of_nonneg_right hfac
          (show 0 ≤ Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) by positivity)
        simpa only [one_mul, mul_assoc] using h
      _ ≤ _ := hcoeff.2.trans (Real.exp_le_exp.mpr hbudget.1)
  obtain ⟨D₁, _hsub, _hspaces, hcorr⟩ :=
    D.exists_controlled_shared_free_refinement E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hcut.1
  obtain ⟨t, ht⟩ := D₁.nonempty
  choose m hm hmb hcorr using hcorr
  have hdenom (d : Fin s) : (m d : ℝ) ≤ Real.exp Λ :=
    (hmb d).trans (Real.exp_le_exp.mpr (hb.2.2.2.trans hAΛ))
  let π := (LinearMap.proj (0 : Fin 4) :
    (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] D.CoefficientFreeLieAlgebra).baseChange ℝ
  have hcommon (d : Fin s) : ∃ γ e q : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
      γ ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
      coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ + e + q ∧
      ‖(E.basis.baseChange ℝ).equivFun e‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
      (E.basis.baseChange ℝ).equivFun q ∈ realDenominatorGrid (m d) := by
    obtain ⟨A, S, hA, hS, hmem⟩ := hcorr d t ht
    let K := fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
    let u := coefficients (v (rankQuadrupleParameters t 1)).log (Finsupp.single () (d.val + 1))
    let γ := coefficients ξ.log (Finsupp.single () (d.val + 1)) - π A - π S
    have hhead : π ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
        (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t)) =
          coefficients ξ.log (Finsupp.single () (d.val + 1)) + u := by
      dsimp only [π]
      rw [real_four_projection, LinearEquiv.apply_symm_apply]
      rfl
    have hproj : π ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
        (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t) - A - S) ∈
          (K.map (LinearMap.proj 0)).baseChange ℝ := by
      rw [realification_map]
      exact ⟨_, hmem, rfl⟩
    rw [map_sub, map_sub, hhead] at hproj
    have hu : u ∈ (K.map (LinearMap.proj 0)).baseChange ℝ :=
      Submodule.baseChange_mono ℝ (dependent_le_refined_firstProjection _ _ _) (hv _ d)
    refine ⟨γ, π A, π S, ?_, ?_, ?_, ?_⟩
    · have h := ((K.map (LinearMap.proj 0)).baseChange ℝ).sub_mem hproj hu
      convert h using 1
      dsimp [γ]
      abel
    · dsimp [γ]
      abel
    · have hA' : ‖((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun A‖ ≤
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ (d.val + 1) := by
        simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using hA
      exact (real_four_projection_norm_le E.basis A 0).trans
        (hA'.trans (div_le_div_of_nonneg_right hnum (by positivity)))
    · exact real_four_projection_grid E.basis S 0 (m d) hS
  choose γ e q hγ heq he hq using hcommon
  exact ⟨m, γ, e, q, fun d => ⟨hm d, hdenom d, hγ d, heq d, he d, hq d⟩⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
