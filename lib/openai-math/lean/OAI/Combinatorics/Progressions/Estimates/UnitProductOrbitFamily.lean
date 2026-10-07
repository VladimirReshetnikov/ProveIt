import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct BigOperators

theorem piRealOrbit_normalized {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (hg : ∀ i, (F i).realification.polynomialOrbitEval w 0 (g i) = 1) :
    (pi F).realification.polynomialOrbitEval w 0 (piRealOrbit F g) = 1 := by
  classical
  apply (realBCHPiEquiv F).injective
  funext i
  change NilpotentLieBCHGroup.realificationMap
    (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot)
    (liePiEval i) ((pi F).realification.polynomialOrbitEval w 0 (piRealOrbit F g)) = _
  rw [piRealOrbit_eval, hg]
  simp only [map_one, Pi.one_apply]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {I : ι → Type*} [∀ i, Fintype (I i)] {w : σ → ℕ}
  (K : ∀ i, I i → (D i).Niltest w)

omit [Nonempty ι] [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_unit
    (hunit : ∀ i x, ∑ j, ‖(K i j).observable x‖ ^ 2 = 1) (x : (pi D).Space) :
    ∑ j : ∀ i, I i, ‖productObservable D (fun i => K i (j i)) x‖ ^ 2 = 1 := by
  classical
  simp only [productObservable, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ i, ∑ j, ‖(K i j).observable (productProjection D i x)‖ ^ 2 :=
      (Fintype.prod_sum (fun i j => ‖(K i j).observable (productProjection D i x)‖ ^ 2)).symm
    _ = ∏ _i : ι, (1 : ℝ) := Finset.prod_congr rfl (fun i _ => hunit i (productProjection D i x))
    _ = 1 := by simp only [Finset.prod_const_one]

theorem exists_normalized_product_unit_family
    (R : ∀ i, (D i).DegreeRankStructure r) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p)
    (hKn : ∀ i j, (K i j).normBound ≤ 1)
    (hKc : ∀ i j, (K i j).ComplexityLE p)
    (hKu : ∀ i x, ∑ j, ‖(K i j).observable x‖ ^ 2 = 1)
    (a : τ → ∀ i, (D i).filtration.realification.PolynomialOrbit w)
    (ha0 : ∀ t i, (D i).filtration.realification.polynomialOrbitEval w 0 (a t i) = 1) :
    (piRank D R).ComplexityLE (productNiltestBudget p) ∧
    ∃ U : (∀ i, I i) → (pi D).Niltest w,
      (∀ j, (U j).normBound = 1) ∧
      (∀ j, (U j).ComplexityLE (productNiltestBudget p)) ∧
      (∀ x, ∑ j, ‖(U j).observable x‖ ^ 2 = 1) ∧
      (∀ t, (pi D).filtration.realification.polynomialOrbitEval w 0
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t)) = 1) ∧
      ∀ t j x, ((U j).withOrbit
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t))).eval x =
          ∏ i, ((K i (j i)).withOrbit (a t i)).eval x := by
  classical
  refine ⟨(piRank_complexity D R hp hι hR).mono _ (productNiltestBudget_geometry hp),
    (fun j => unitBoundedPiNiltest D (fun i => K i (j i)) hp hι
      (fun i => hKc i (j i)) (fun i => hKn i (j i))),
    (fun _ => rfl), (fun j => unitBoundedPiNiltest_complexity D _ hp hι _ _),
    (fun x => productObservable_unit D K hKu x),
    (fun t => NilpotentLieFiltration.piRealOrbit_normalized _ _ (ha0 t)), ?_⟩
  intro t j x
  change (∏ i, (K i (j i)).observable (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
      (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t)))))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  exact congrArg (fun g : (D i).RealGroup => (K i (j i)).observable (QuotientGroup.mk g))
    (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) (a t) x i)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
