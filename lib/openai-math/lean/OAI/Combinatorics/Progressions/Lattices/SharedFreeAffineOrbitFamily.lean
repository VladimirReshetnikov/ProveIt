/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FreeCoefficientCorrectionControl
import OAI.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
import OAI.Combinatorics.Progressions.Polynomial.DegreewiseAffineRecovery
import OAI.Combinatorics.Progressions.Polynomial.DegreewiseProperAffineRecovery

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

theorem affine_petal_decomposition
    {μ ι V : Type*} [Fintype μ] [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (ι → ℚ)) (hker : LinearMap.ker ℓ = K)
    (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (hσU : ∀ y, σ y ∈ U.baseChange ℝ)
    (hσ : ∀ w ∈ U.baseChange ℝ,
      realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (σ (realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w)) =
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤ C * ‖y‖)
    {l m : ℕ} (hgrid : ∀ y ∈ realDenominatorGrid l,
      (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m)
    {r : ℕ} (α : ι → ℝ) (β : Fin r → ι → ℝ) (x : Fin r → ℤ)
    (w : ℝ ⊗[ℚ] V) (hw : w ∈ U.baseChange ℝ) (q : ι → ℝ)
    (hq : q ∈ realDenominatorGrid l) {ε : ℝ}
    (he : ‖realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w -
      (α + ∑ j, (x j : ℝ) • β j) - q‖ ≤ ε) :
    ∃ E Q P : ℝ ⊗[ℚ] V, E ∈ U.baseChange ℝ ∧ Q ∈ U.baseChange ℝ ∧
      P ∈ (fourPetalSpace U K).baseChange ℝ ∧
      w = (σ α + ∑ j, (x j : ℝ) • σ (β j)) + E + Q + P ∧
      ‖(b.baseChange ℝ).equivFun E‖ ≤ C * ε ∧
      (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m := by
  let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)
  let a := realifyCoordinateMap φ w
  let e := a - (α + ∑ j, (x j : ℝ) • β j) - q
  let P := w - σ a
  have hPU : P ∈ U.baseChange ℝ := (U.baseChange ℝ).sub_mem hw (hσU a)
  have hzero : realifyCoordinateMap φ P = 0 := by
    change realifyCoordinateMap φ (w - σ a) = 0
    rw [map_sub, hσ w hw, sub_self]
  have hP : P ∈ (fourPetalSpace U K).baseChange ℝ := by
    apply (mem_real_petal_annihilator_iff U K ℓ hker P).mpr
    refine ⟨hPU, fun j => ?_⟩
    exact congrFun hzero j
  refine ⟨σ e, σ q, P, hσU e, hσU q, hP, ?_, ?_, hgrid q hq⟩
  · dsimp [P, e]
    simp only [map_sub, map_add, map_sum, map_smul]
    abel
  · exact (hbound e).trans (mul_le_mul_of_nonneg_left he hC)

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

theorem exists_shared_free_affine_recovery
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ (n : Fin s → ℕ)
        (ℓ : ∀ d : Fin s, (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin (n d) → ℚ))
        (m : Fin s → ℕ),
        (∀ d, n d ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
          Function.Surjective (ℓ d) ∧ LinearMap.ker (ℓ d) =
            fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
          (∀ k i j, rationalLogHeight (ℓ d (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
              fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
          0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ) ∧
        let a := fun h (d : Fin s) => realifyCoordinateMap
          ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
          (coefficients (v h).log (Finsupp.single () (d.val + 1)))
        let n₀ := Fintype.card (Σ d : Fin s, Fin (n d))
        (n₀ : ℝ) ≤ 4 * (s : ℝ) * P' ∧
        ∃ J ⊆ H', J.Nonempty ∧
          Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
          ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N)
            (h₀ : ZMod N) (α : ∀ d, Fin (n d) → ℝ) (β : Fin r₀ → ∀ d, Fin (n d) → ℝ),
            (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧
            (∀ d i, α d i ∈ Set.Ico (0 : ℝ) (1 / m d)) ∧
            (∀ j d i, β j d i ∈ Set.Ico (0 : ℝ) (1 / m d)) ∧
            ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
              (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
              ∀ d, ∃ q ∈ realDenominatorGrid (m d),
                ‖a h d - (α d + ∑ j, (x j : ℝ) • β j d) - q‖ ≤
                  Real.exp Λ / (N : ℝ) ^ (d.val + 1) := by
  intro B Λ
  classical
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let z₀ := 8 * sharedRefinementInputBudget s P' + 1
  let A := sharedFreeEquationInputBudget s Q P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hbudget₀ := (sharedFreeAffineConstant_spec s).2 Q P' hQ hQP' hP' 0
    (by simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg s)) hP')
  have hcut := sharedFreeRecoveryThreshold_spec s hQ hP' N
    ((Real.exp_le_exp.mpr hbudget₀.1).trans hN)
  have hcoeff := sharedFreeRecoveryThreshold_coefficient_bounds s hQ hP'
  obtain ⟨D₁, hsub, hspaces, hblocks⟩ :=
    D.exists_controlled_shared_free_equations E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hcut.1
  choose n hn ℓ hsurj hker hheight m hm hmA hnear using hblocks
  have hdenom (d : Fin s) : (m d : ℝ) ≤ Real.exp Λ :=
    (hmA d).trans (Real.exp_le_exp.mpr (hcoeff.1.trans hbudget₀.1))
  have hnum : 2 * (Real.exp ((A + 2) ^ 3) *
      (Real.exp z₀ + Real.exp ((z₀ + 2) ^ 3 + (z₀ + 2) ^ 18 + z₀))) ≤ Real.exp Λ :=
    hcoeff.2.trans (Real.exp_le_exp.mpr hbudget₀.1)
  let a := fun h (d : Fin s) => realifyCoordinateMap
    ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
    (coefficients (v h).log (Finsupp.single () (d.val + 1)))
  let c := fun d : Fin s => realifyCoordinateMap ((ℓ d).comp (fourDiagonalMap (R := ℚ)))
    (coefficients ξ.log (Finsupp.single () (d.val + 1)))
  let ε := fun d : Fin s => Real.exp ((A + 2) ^ 3) *
    ((Real.exp z₀ + Real.exp ((z₀ + 2) ^ 3 + (z₀ + 2) ^ 18 + z₀)) / (N : ℝ) ^ (d.val + 1))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hε : ∀ d, 0 < ε d := by intro d; dsimp [ε]; positivity
  have hsmall : ∀ d, 2 * (m d : ℝ) * ε d ≤ 1 := by
    intro d
    exact hcut.2 (m d) (d.val + 1) (by omega) (hmA d)
  have hnear' : ∀ t ∈ D₁.quadruples, ∀ d, ∃ q ∈ realDenominatorGrid (m d),
      ‖c d + (a (rankQuadrupleParameters t 1) d + a (rankQuadrupleParameters t 2) d -
        a (rankQuadrupleParameters t 0) d - a (rankQuadrupleParameters t 3) d) - q‖ ≤ ε d := by
    intro t ht d
    simpa only [a, c, ε, monomialScale, Finsupp.prod_single_index, pow_zero] using hnear d t ht
  have hdim : (Fintype.card (Σ d : Fin s, Fin (n d)) : ℝ) ≤ 4 * (s : ℝ) * P' := by
    rw [Fintype.card_sigma, Nat.cast_sum]
    simp only [Fintype.card_fin]
    calc
      (∑ d : Fin s, (n d : ℝ)) ≤ ∑ _d : Fin s, 4 * P' := by
        apply Finset.sum_le_sum
        intro d _hd
        have hnR := (Nat.cast_le (α := ℝ)).mpr (hn d)
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hnR
        exact hnR.trans (mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  refine ⟨D₁, hsub, hspaces, n, ℓ, m, ?_, hdim, ?_⟩
  · intro d
    exact ⟨hn d, hsurj d, hker d, hheight d, hm d, hdenom d⟩
  · obtain ⟨J, hJH, hJ, hsize, r₀, R₀, η, h₀, α, β, hrank, hproper, hα, hβ, hrepr⟩ :=
      D₁.degreewise_proper_affine_recovery hB a c m hm ε hε hsmall hnear'
    have hbudget := sharedFreeAffineConstant_proper_spec s hP' _ hdim
    refine ⟨J, hJH, hJ, ?_, r₀, R₀, η, h₀, α, β, hrank.trans hbudget.2.2, hproper, hα, hβ, ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hbudget.1)) (Nat.cast_nonneg _)).trans hsize
    · intro h hh
      obtain ⟨x, hx, hspace, herr⟩ := hrepr h hh
      refine ⟨x, hx, hspace, ?_⟩
      intro d
      obtain ⟨q, hq, he⟩ := herr d
      refine ⟨q, hq, he.trans ?_⟩
      simpa only [ε, mul_div_assoc] using
        div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg N) (d.val + 1))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreePetalLiftInput (s : ℕ) (q p : ℝ) : ℝ :=
  4 * p + fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) +
    (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s

noncomputable def sharedFreePetalLiftBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let t := (sharedFreePetalLiftInput s q p + 2) ^ 4 + 1
  (t + 2) ^ 3 + (t + 2) ^ 36 + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s

end Erdos3

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

theorem exists_shared_free_affine_petal
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let L := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : Fin s → ℕ) (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ (∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp L) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp L) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp L) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∀ d, ∃ e q u : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
              e ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
              q ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
              u ∈ (fourPetalSpace (D.dependentFreeSpan d)
                (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                  (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ ∧
              coefficients (v h).log (Finsupp.single () (d.val + 1)) =
                (α d + ∑ j, (x j : ℝ) • β j d) + e + q + u ∧
              ‖(E.basis.baseChange ℝ).equivFun e‖ ≤ Real.exp L / (N : ℝ) ^ (d.val + 1) ∧
              (E.basis.baseChange ℝ).equivFun q ∈ realDenominatorGrid (m d) := by
  intro B Λ L
  classical
  obtain ⟨D₁, hsub, hspaces, n, ℓ, l, hdata, _hdim, J, hJH, hJ, hcard,
      r₀, R₀, η, h₀, α, β, hrank, hproper, hα, hβ, hrepr⟩ :=
    D.exists_shared_free_affine_recovery E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let A := sharedFreePetalLiftInput s Q P'
  let t := (A + 2) ^ 4 + 1
  let C := (t + 2) ^ 3 + (t + 2) ^ 18
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have ha : 0 ≤ fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P') :=
    fourRefinementAnnihilatorBudget_nonneg (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP'))
  have hA : 0 ≤ A := by dsimp [A, sharedFreePetalLiftInput]; positivity
  have h4A : 4 * P' ≤ A := by dsimp [A, sharedFreePetalLiftInput]; linarith
  have hPA : P' ≤ A := by linarith
  have hQA : Q ≤ A := hQP'.trans hPA
  have hΛA : Λ ≤ A := by dsimp [A, sharedFreePetalLiftInput]; linarith
  have haA : fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P') ≤ A := by
    dsimp [A, sharedFreePetalLiftInput]
    linarith
  have hsections (d : Fin s) :
      ∃ (σ : (Fin (n d) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
        (∀ y, σ y ∈ (D.dependentFreeSpan d).baseChange ℝ) ∧
        (∀ w ∈ (D.dependentFreeSpan d).baseChange ℝ,
          realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
              (σ (realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
                (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) w)) =
            realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
              (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) w) ∧
        (∀ y, ‖(E.basis.baseChange ℝ).equivFun (σ y)‖ ≤ Real.exp C * ‖y‖) ∧
        ∀ y ∈ realDenominatorGrid (l d),
          (E.basis.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
    obtain ⟨c, hc⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
    obtain ⟨hn, _hsurj, _hker, hheight, hl, hlΛ⟩ := hdata d
    have hcspan : Submodule.span ℚ (Set.range (fun j => (c j : D.CoefficientFreeLieAlgebra))) =
        D.dependentFreeSpan d := by
      change Submodule.span ℚ (Set.range ((D.dependentFreeSpan d).subtype ∘ c)) = _
      rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
    apply exists_logHeight_subspace_image_section E.basis (D.dependentFreeSpan d)
      (fun j => (c j : D.CoefficientFreeLieAlgebra)) hcspan
      ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
      (l d) hl hA
    · simpa only [Fintype.card_fin] using (hT.1.1.trans hQP').trans hPA
    · have hnR := (Nat.cast_le (α := ℝ)).mpr hn
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hnR
      have hdim := mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num : (0 : ℝ) ≤ 4)
      simpa only [Fintype.card_fin] using hnR.trans (hdim.trans h4A)
    · have hcR : (finrank ℚ (D.dependentFreeSpan d) : ℝ) ≤
          finrank ℚ D.CoefficientFreeLieAlgebra := by
        exact_mod_cast Submodule.finrank_le (D.dependentFreeSpan d)
      simpa only [Fintype.card_fin] using hcR.trans ((hT.1.1.trans hQP').trans hPA)
    · intro j i
      exact (hc j i).trans hQA
    · intro i j
      exact (hheight 0 i j).trans haA
    · exact hlΛ.trans (Real.exp_le_exp.mpr hΛA)
  choose σ m hm hmb hσU hσfix hσnorm hσgrid using hsections
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have h18 : (t + 2) ^ 18 ≤ (t + 2) ^ 36 := pow_le_pow_right₀ (by linarith) (by decide)
  have hL : L = (t + 2) ^ 3 + (t + 2) ^ 36 + Λ := rfl
  have hCL : C + Λ ≤ L := by dsimp [C]; rw [hL]; linarith
  have hCL' : C ≤ L := (le_add_of_nonneg_right hΛ).trans hCL
  have hunit (d : Fin s) (y : Fin (n d) → ℝ)
      (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) (1 / l d)) : ‖y‖ ≤ 1 := by
    have hl : 0 < l d := (hdata d).2.2.2.2.1
    have hlR : (0 : ℝ) < l d := by exact_mod_cast hl
    have hl1 : (1 : ℝ) ≤ l d := by exact_mod_cast hl
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hy i).1]
    exact (hy i).2.le.trans ((div_le_one hlR).mpr hl1)
  have hσunit (d : Fin s) (y : Fin (n d) → ℝ)
      (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) (1 / l d)) :
      ‖(E.basis.baseChange ℝ).equivFun (σ d y)‖ ≤ Real.exp L := by
    calc
      _ ≤ Real.exp C * ‖y‖ := hσnorm d y
      _ ≤ Real.exp C * 1 := mul_le_mul_of_nonneg_left (hunit d y hy) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact Real.exp_le_exp.mpr hCL'
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m,
    (fun d => σ d (α d)), (fun j d => σ d (β j d)), hrank, hproper, ?_, ?_, ?_, ?_⟩
  · intro d
    exact ⟨hm d, (hmb d).trans (Real.exp_le_exp.mpr (by rw [hL]; linarith))⟩
  · intro d
    exact ⟨hσU d _, hσunit d _ (hα d)⟩
  · intro j d
    exact ⟨hσU d _, hσunit d _ (hβ j d)⟩
  · intro h hh
    obtain ⟨x, hx, hspace, herr⟩ := hrepr h hh
    refine ⟨x, hx, hspace, ?_⟩
    intro d
    obtain ⟨q, hq, he⟩ := herr d
    obtain ⟨e, q', u, heU, hqU, hu, heq, hbound, hgrid⟩ :=
      affine_petal_decomposition E.basis (D.dependentFreeSpan d) _ (ℓ d) (hdata d).2.2.1
        (σ d) (hσU d) (hσfix d) (Real.exp_pos _).le (hσnorm d) (hσgrid d)
        (α d) (fun j => β j d) x (coefficients (v h).log (Finsupp.single () (d.val + 1)))
        (hv h d) q hq he
    refine ⟨e, q', u, heU, hqU, hu, heq, hbound.trans ?_, hgrid⟩
    calc
      Real.exp C * (Real.exp Λ / (N : ℝ) ^ (d.val + 1)) =
          Real.exp (C + Λ) / (N : ℝ) ^ (d.val + 1) := by rw [← mul_div_assoc, ← Real.exp_add]
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCL) (by positivity)

end Erdos3.NativeRankRelation.CommonData

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

theorem exists_shared_free_affine_orbit_family
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let L := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp L) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp L) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∃ A ε ρ U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
              A.log = positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ)) (Real.exp L) ε.log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
              ∀ d : Fin s,
                coefficients U.log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ ∧
                coefficients (v h).log (Finsupp.single () (d.val + 1)) =
                  coefficients A.log (Finsupp.single () (d.val + 1)) +
                  coefficients ε.log (Finsupp.single () (d.val + 1)) +
                  coefficients ρ.log (Finsupp.single () (d.val + 1)) +
                  coefficients U.log (Finsupp.single () (d.val + 1)) := by
  intro B Λ L
  classical
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, l, α, β,
      hrank, hproper, hl, hα, hβ, hrepr⟩ :=
    D.exists_shared_free_affine_petal E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let m := ∏ d, l d
  have hm : 0 < m := Finset.prod_pos (fun d _ => (hl d).1)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    change ((∏ d, l d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _d : Fin s, Real.exp L :=
        Finset.prod_le_prod₀ (fun d _ => Nat.cast_nonneg (l d)) (fun d _ => (hl d).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, α, β,
    hrank, hproper, hm, hmb, hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, hcoeff⟩ := hrepr h hh
  choose e q u he hq hu heq herr hgrid using hcoeff
  have hdep (d : Fin s) :=
    Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_coefficientFreeSpan d)
  have ha (d : Fin s) : α d + ∑ j, (x j : ℝ) • β j d ∈
      (D.coefficientFreeSpan d).baseChange ℝ := by
    apply hdep d
    exact Submodule.add_mem _ (hα d).1
      (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d).1))
  have huC (d : Fin s) : u d ∈ (D.coefficientFreeSpan d).baseChange ℝ :=
    hdep d (Submodule.baseChange_mono ℝ inf_le_left (hu d))
  obtain ⟨A, hA, hA0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil _ ha
  obtain ⟨ε, hε, hε0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil e
    (fun d => hdep d (he d))
  obtain ⟨ρ, hρ, hρ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil q
    (fun d => hdep d (hq d))
  obtain ⟨U, hU, hU0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil u huC
  refine ⟨x, hx, hspace, A, ε, ρ, U, hA, hA0, hε0, hρ0, hU0, ?_, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (E.basis.baseChange ℝ) e
      (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_pos L).le
    intro d
    simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using herr d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    exact fun d => realDenominatorGrid_subset_of_dvd (hl d).1 (hdiv d) (hgrid d)
  · intro d
    rw [hA, hε, hρ, hU, positiveUnivariate_coefficient, positiveUnivariate_coefficient,
      positiveUnivariate_coefficient, positiveUnivariate_coefficient]
    exact ⟨hu d, heq d⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
