/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.NormalizedMarkedPhase

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

theorem markedShiftEval_lie_of_zero_phase (a : Fin t → ℚ)
    (p q : markedShiftSubalgebra F v w marked t)
    (hp : p.val.right = 0) (hq : q.val.right = 0) :
    markedShiftEval F v w marked t a ⁅p, q⁆ =
      ⁅markedShiftEval F v w marked t a p, markedShiftEval F v w marked t a q⁆ := by
  have hz (p : VectorPolynomial (Fin t) ℚ L) : directionalDerivative (0 : Fin t → ℚ) p = 0 := by
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  change eval a (⁅p.val.left.val, q.val.left.val⁆ + directionalDerivative p.val.right q.val.left.val -
    directionalDerivative q.val.right p.val.left.val) = ⁅eval a p.val.left.val, eval a q.val.left.val⁆
  rw [hp, hq]
  change eval a (⁅p.val.left.val, q.val.left.val⁆ +
    directionalDerivative (0 : Fin t → ℚ) q.val.left.val -
    directionalDerivative (0 : Fin t → ℚ) p.val.left.val) = _
  rw [hz, hz, add_zero, sub_zero]
  exact (evalLie a).map_lie _ _

variable (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)

noncomputable def markedBaseEvaluation (a : Fin t → ℚ) :
    MarkedShiftQuotient F v w marked t →ₗ[ℚ] (L ⧸ J) :=
  (markedShiftSecondIdeal F v w marked t).toSubmodule.liftQ
    ((lieQuotientMap J).toLinearMap.comp (markedShiftEval F v w marked t a)) (by
      intro p hp
      exact (lieQuotientMap_eq_zero J _).mpr (hJ (markedPolynomialLayer_eval_mem v w marked hp.2 a)))

theorem markedBaseEvaluation_map (a : Fin t → ℚ) (p : markedShiftSubalgebra F v w marked t) :
    markedBaseEvaluation F v w marked t J hJ a (lieQuotientMap (markedShiftSecondIdeal F v w marked t) p) =
      lieQuotientMap J (markedShiftEval F v w marked t a p) := rfl

theorem markedBaseEvaluation_lie (a : Fin t → ℚ) (x y : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) (hy : markedQuotientPhase F v w marked t y = 0) :
    markedBaseEvaluation F v w marked t J hJ a ⁅x, y⁆ =
      ⁅markedBaseEvaluation F v w marked t J hJ a x, markedBaseEvaluation F v w marked t J hJ a y⁆ := by
  obtain ⟨p, hp, rfl⟩ := exists_zero_phase_lift F v w marked t x hx
  obtain ⟨q, hq, rfl⟩ := exists_zero_phase_lift F v w marked t y hy
  rw [← (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).map_lie]
  change lieQuotientMap J (markedShiftEval F v w marked t a ⁅p, q⁆) =
    ⁅lieQuotientMap J (markedShiftEval F v w marked t a p),
      lieQuotientMap J (markedShiftEval F v w marked t a q)⁆
  rw [markedShiftEval_lie_of_zero_phase F v w marked t a p q hp hq]
  exact (lieQuotientMap J).map_lie _ _

noncomputable def markedBaseEvaluationLie (a : Fin t → ℚ) :
    markedQuotientPolynomialAlgebra F v w marked t →ₗ⁅ℚ⁆ (L ⧸ J) where
  toLinearMap := (markedBaseEvaluation F v w marked t J hJ a).comp
    (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.subtype
  map_lie' {x y} := markedBaseEvaluation_lie F v w marked t J hJ a x.val y.val x.property y.property

theorem markedBaseEvaluationLie_apply (a : Fin t → ℚ)
    (x : markedQuotientPolynomialAlgebra F v w marked t) :
    markedBaseEvaluationLie F v w marked t J hJ a x =
      markedBaseEvaluation F v w marked t J hJ a x.val := rfl

theorem markedBaseEvaluation_real_map (a : Fin t → ℚ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p) =
      (lieQuotientMap J).toLinearMap.baseChange ℝ ((markedShiftEval F v w marked t a).baseChange ℝ p) := by
  induction p using TensorProduct.inductionOn with
  | tmul c p =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

def monoidHomOfSurjectiveComposition {A B C : Type*} [Monoid A] [Monoid B] [Monoid C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C) (k : B → C)
    (hcomp : ∀ a, k (f a) = g a) : B →* C where
  toFun := k
  map_one' := by
    calc
      k 1 = k (f 1) := congrArg k f.map_one.symm
      _ = g 1 := hcomp 1
      _ = 1 := g.map_one
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← f.map_mul, hcomp, hcomp, hcomp, g.map_mul]

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e) (a : Fin t → ℚ)

theorem markedBaseEvaluation_real_incl
    (z : ℝ ⊗[ℚ] markedQuotientPolynomialAlgebra F v w marked t) :
    (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ
      ((markedQuotientPolynomialAlgebra F v w marked t).incl.toLinearMap.baseChange ℝ z) =
      (markedBaseEvaluationLie F v w marked t J hJ a).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.inductionOn with
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def markedPureEvaluation
    (g : realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)) : E.RealGroup :=
  ⟨(markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ g.val.coord⟩

theorem markedPureEvaluation_inclusion
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] markedQuotientPolynomialAlgebra F v w marked t) (s + 1)
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot
        D.filtration.lowerCentralSeries_eq_bot (markedQuotientPolynomialAlgebra F v w marked t)))) :
    markedPureEvaluation F v w marked t D J hJ E a
      (realificationSubgroupHom (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t) g) =
      realificationMap
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot
          (markedQuotientPolynomialAlgebra F v w marked t))
        (hM := E.filtration.lowerCentralSeries_eq_bot)
        (markedBaseEvaluationLie F v w marked t J hJ a) g := by
  apply NilpotentLieBCHGroup.ext
  exact markedBaseEvaluation_real_incl F v w marked t J hJ a g.coord

noncomputable def markedPureEvaluationHom :
    realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) →* E.RealGroup :=
  monoidHomOfSurjectiveComposition
    (realificationSubgroupHom (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t))
    (realificationSubgroupHom_surjective (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t))
    (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot
        (markedQuotientPolynomialAlgebra F v w marked t))
      (hM := E.filtration.lowerCentralSeries_eq_bot) (markedBaseEvaluationLie F v w marked t J hJ a))
    (markedPureEvaluation F v w marked t D J hJ E a)
    (markedPureEvaluation_inclusion F v w marked t D J hJ E a)

theorem markedPureEvaluationHom_coord
    (g : realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)) :
    (markedPureEvaluationHom F v w marked t D J hJ E a g).coord =
      (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ g.val.coord := rfl

variable (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
  (⟨(markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

include hmap in
theorem markedPureEvaluationHom_lattice :
    D.realLattice.comap (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)).subtype ≤
        E.realLattice.comap (markedPureEvaluationHom F v w marked t D J hJ E a) := by
  intro g hg
  exact hmap g.val hg

noncomputable def markedPureSpaceMap :
    (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) ⧸
        D.realLattice.comap (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (markedQuotientPolynomialAlgebra F v w marked t)).subtype) → E.Space :=
  cosetMap _ _ (markedPureEvaluationHom F v w marked t D J hJ E a)
    (markedPureEvaluationHom_lattice F v w marked t D J hJ E a hmap)

theorem markedPureSpaceMap_mk
    (g : realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)) :
    markedPureSpaceMap F v w marked t D J hJ E a hmap (QuotientGroup.mk g) =
      QuotientGroup.mk (markedPureEvaluationHom F v w marked t D J hJ E a g) := rfl

end Erdos3

end

end OAI
