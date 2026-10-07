import OAI.Combinatorics.Progressions.Dynamics.StepOneSplittingBudget
import OAI.Combinatorics.Progressions.Linear.StepOneGradedKernel

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

theorem stepOne_vertical_character {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L 1) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hf : ∀ z : F.realification.Group, z ∈ F.realification.subgroup 1 → ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (g : F.realification.Group) :
    f (QuotientGroup.mk g) = character ((realifyFunctional η g.coord : ℝ) : CircleFourier.Circle) *
      f (QuotientGroup.mk (1 : F.realification.Group)) := by
  have hg : g ∈ F.realification.subgroup 1 := by rw [F.realification.subgroup_one]; trivial
  simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
    hf g hg (QuotientGroup.mk (1 : F.realification.Group))

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

omit [DecidableEq σ] in
theorem stepOne_niltest_eval_affine (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    (hP : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (x : σ → ℤ) :
    P.eval x = P.observable (QuotientGroup.mk (1 : D.RealGroup)) *
      character (((realifyFunctional η (coefficients P.orbit.log 0) +
        ∑ i, (x i : ℝ) * realifyFunctional η (coefficients P.orbit.log (Finsupp.single i 1))) : ℝ) :
          CircleFourier.Circle) := by
  rw [Niltest.eval, ← D.filtration.realification.polynomialOrbitRealEval_integer]
  rw [stepOne_vertical_character D.filtration D.realLattice η P.observable hP,
    D.filtration.realification.polynomialOrbitRealEval_coord,
    eval₂_affine_of_degreeLE_one P.orbit.log P.orbit.degreeLE]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rw [mul_comm]

theorem stepOne_niltest_linear_phase_bias (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    (hP : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) {M δ : ℝ} (hM : 0 < M)
    (hbound : (P.normBound : ℝ) ≤ M) (hbias : δ ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    δ / M ≤ ‖linearPhaseMean T (fun i =>
      (realifyFunctional η (coefficients P.orbit.log (Finsupp.single i 1)) : CircleFourier.Circle))‖ := by
  apply linearPhaseMean_norm_ge_of_affine_bias T
    (P.observable (QuotientGroup.mk (1 : D.RealGroup)))
    (realifyFunctional η (coefficients P.orbit.log 0) : CircleFourier.Circle) _ hM
    ((P.norm_le _).trans hbound)
  rw [integerBox_expect_eq_fin] at hbias
  convert hbias using 2
  apply Finset.expect_congr rfl
  intro t _
  rw [D.stepOne_niltest_eval_affine P η hP]
  congr 2
  have hcoe (f : σ → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) = ∑ i, (f i : CircleFourier.Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
  simp only [Int.cast_natCast, AddCircle.coe_add, hcoe, ← nsmul_eq_mul, AddCircle.coe_nsmul]

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem exists_stepOne_niltest_splitting (P : D.Niltest (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p) (hP : P.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    ∃ (m : ℕ) (E Q R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (v : Fin d → L),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      D.filtration.realification.polynomialSymbolHom (fun _ => 1) (E * Q * R) =
        D.filtration.realification.polynomialSymbolHom (fun _ => 1) ⟨⟨P.orbit.log, P.orbit.property⟩⟩ ∧
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) (fun i => (T i : ℝ))
        (Real.exp ((p + 2) ^ 4)) E ∧
      D.filtration.PolynomialRationalGrid D.basis (fun _ => 1) m R ∧
      Submodule.span ℚ (Set.range v) = (D.filtration.stepOneFrequencyKernel η).toSubmodule ∧
      (∀ i j, rationalLogHeight (D.basis.repr (v i) j) ≤ (p + 2) ^ 4) ∧
      (∀ t : σ → ℝ, eval₂ t (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
        realificationLieSubalgebra (D.filtration.stepOneFrequencyKernel η)) ∧
      coefficients (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hheight : ∀ i, RationalHeightLE (η (D.basis i)) H :=
    fun i => rationalHeightLE_ceil_exp (hηheight i)
  have hnorm : (P.normBound : ℝ) ≤ Real.exp p := by
    have h := P.observable_budget hP
    have hl := P.lipBound.coe_nonneg
    linarith
  have hphase := D.stepOne_niltest_linear_phase_bias P η hvertical T (Real.exp_pos p) hnorm hbias
  obtain ⟨m, E, Q, R, hm, hmH, hsum, he, hr, hq, hq0⟩ :=
    D.filtration.exists_stepOne_linear_splitting D.basis η hH hheight T hT
      (fun i => coefficients P.orbit.log (Finsupp.single i 1))
      (div_pos (Real.exp_pos (-p)) (Real.exp_pos p)) hphase
  obtain ⟨v, hvspan, hvheight⟩ := exists_bounded_frequency_kernel_spanning D.basis η hH hheight
  refine ⟨m, E, Q, R, v, hm, (Nat.cast_le.mpr hmH).trans (stepOne_denominator_budget hp), ?_, ?_, hr,
    hvspan, ?_, hq, hq0⟩
  · rw [hsum]
    apply NilpotentLieBCHGroup.ext
    exact D.filtration.realification.stepOne_symbol_linearPart ⟨P.orbit.log, P.orbit.property⟩
  · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) (fun i => (T i : ℝ))
      (fun i => Nat.cast_pos.mpr (hT i)) (stepOne_slow_budget hp) E he
  · intro i j
    exact rationalLogHeight_le_of_height
      (hvheight i j) (stepOne_kernel_height_budget hp)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem exists_stepOne_graded_niltest_splitting
    (ω : Fin d → ℕ)
    (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hP : P.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    ∃ (m : ℕ) (E Q R : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : Fin d → D.filtration.AssociatedGraded),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      E * Q * R = D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1)
        ⟨⟨P.orbit.log, P.orbit.property⟩⟩ ∧
      D.filtration.SymbolSlowBound D.basis ω hlayers (fun _ => 1) (fun i => (T i : ℝ))
        (Real.exp ((p + 2) ^ 4)) E ∧
      D.filtration.SymbolRationalGrid D.basis ω hlayers (fun _ => 1) m R ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hlayers) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        ((D.filtration.associatedGradedBasis D.basis ω hlayers).repr (v i) j) ≤ (p + 2) ^ 4) ∧
      (∀ x ∈ W, D.filtration.stepOneGradedFrequency D.basis ω hlayers η x = 0) ∧
      (∀ t : σ → ℝ, eval₂ t
        (D.filtration.realGradedSymbolPolynomial D.basis ω hlayers (fun _ => 1) Q.coord) ∈
          realificationLieSubalgebra W) := by
  obtain ⟨m, E, Q, R, v, hm, hmbound, hsymbol, he, hr, hvspan, hvheight, hq, _⟩ :=
    D.exists_stepOne_niltest_splitting P η hp hP hηheight hvertical T hT hbias
  refine ⟨m,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) E,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) Q,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) R,
    D.filtration.stepOneGradedKernel D.basis ω hlayers η,
    (fun i => D.filtration.stepOneGradedEquiv D.basis ω hlayers (v i)),
    hm, hmbound, ?_,
    D.filtration.polynomialSlowBound_symbol D.basis ω hlayers (fun _ => 1) _ _ E he,
    D.filtration.polynomialRationalGrid_symbol D.basis ω hlayers (fun _ => 1) m R hr,
    D.filtration.stepOneGradedKernel_span D.basis ω hlayers η v hvspan,
    D.filtration.stepOne_graded_submodule D.basis ω hlayers _, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    exact D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq D.basis ω hlayers
      (fun _ => 1) _ _ hsymbol
  · intro i j
    rw [D.filtration.stepOneGradedEquiv_coordinate]
    exact hvheight i j
  · intro x hx
    exact (D.filtration.mem_stepOneGradedKernel D.basis ω hlayers η x).mp hx
  · exact D.filtration.stepOne_symbol_values_in_gradedKernel D.basis ω hlayers η
      (fun _ => 1) (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hq

end Erdos3.RationalFilteredNilmanifold

end

end OAI
