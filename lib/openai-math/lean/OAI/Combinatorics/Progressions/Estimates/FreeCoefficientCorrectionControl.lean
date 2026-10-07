/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Polynomial.NativeFreePolynomialLifts

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem exists_native_freeCoefficientPolynomialOrbit
    (v : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ d, v d ∈ (D.coefficientFreeSpan d).baseChange ℝ) :
    ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      u.log = positiveUnivariate v ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 := by
  have hfil := D.coefficientFreeRealFiltration_eq_native E T hT
  have hlayer (d : Fin s) : v d ∈ E.filtration.realification.layer (d.val + 1) := by
    rw [← hfil]
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.coefficientFreeSpan_le_layer d) (hv d)
  have hadapt : E.filtration.realification.Adapted (fun _ : Unit => 1)
      (positiveUnivariate v) := by
    apply (E.filtration.realification.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hlayer d
  let u := NilpotentLieFiltration.polynomialOrbitOfLog (positiveUnivariate v) hadapt
  refine ⟨u, rfl, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
  rw [eval_zero_eq_coefficient, positiveUnivariate_zero]

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

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem exists_native_freeCoefficient_corrections
    (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hγ : ∀ d, γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (he : ∀ d, e d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (hq : ∀ d, q d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (l : Fin s → ℕ) (hl : ∀ d, 0 < l d) {L : ℝ}
    (hlb : ∀ d, (l d : ℝ) ≤ Real.exp L)
    (herr : ∀ d, ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤
      Real.exp L / (N : ℝ) ^ (d.val + 1))
    (hgrid : ∀ d, (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (l d)) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧ (∀ d, l d ∣ m) ∧
      ∃ Γ ε ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        Γ.log = positiveUnivariate γ ∧ ε.log = positiveUnivariate e ∧
        ρ.log = positiveUnivariate q ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
        CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
          (Real.exp L) ε.log ∧
        CoefficientGrid (E.basis.baseChange ℝ) m ρ.log := by
  classical
  obtain ⟨Γ, hΓ, hΓ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT γ hγ
  obtain ⟨ε, hε, hε0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT e he
  obtain ⟨ρ, hρ, hρ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT q hq
  let m := ∏ d, l d
  have hm : 0 < m := Finset.prod_pos (fun d _ => hl d)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    change ((∏ d, l d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _d : Fin s, Real.exp L :=
        Finset.prod_le_prod₀ (fun d _ => Nat.cast_nonneg (l d)) (fun d _ => hlb d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨m, hm, hmb, hdiv, Γ, ε, ρ, hΓ, hε, hρ, hΓ0, hε0, hρ0, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (E.basis.baseChange ℝ) e
      (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_pos L).le
    intro d
    simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using herr d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    intro d
    exact realDenominatorGrid_subset_of_dvd (hl d) (hdiv d) (hgrid d)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
