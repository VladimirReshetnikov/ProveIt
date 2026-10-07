/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Combinatorics.Progressions.Estimates.NativeDilationObservable
import OAI.Combinatorics.Progressions.Estimates.NormalizedComparisonOrbit
import OAI.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}

noncomputable def tensorPower (V : D.UnitVerticalObservable T I p) (n : ℕ) :
    D.UnitVerticalObservable T (Fin n → I) (p + n + 1) where
  observable a x := ∏ j, V.observable (a j) x
  unit x := by
    simp only [norm_prod, ← Finset.prod_pow]
    calc
      _ = ∏ _j : Fin n, ∑ a : I, ‖V.observable a x‖ ^ 2 := (Fintype.prod_sum _).symm
      _ = 1 := by simp only [V.unit, Finset.prod_const_one]
  norm a x := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => V.norm (a j) x)
  lipBound := n * V.lipBound
  lip_bound := by
    change (n : ℝ) * V.lipBound ≤ Real.exp (p + n + 1)
    calc
      _ ≤ Real.exp ((n : ℝ) + 1) * Real.exp p :=
        mul_le_mul (by linarith [Real.add_one_le_exp ((n : ℝ) + 1)]) V.lip_bound
          V.lipBound.coe_nonneg (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  lipschitz := by
    let := D.metricSpace
    intro a
    have h := bounded_lipschitz_fintype_prod (fun j x => V.observable (a j) x)
      (B := 1) le_rfl (fun j => V.lipschitz (a j)) (fun j x => V.norm (a j) x)
    simpa only [Fintype.card_fin, one_pow, mul_one] using h.2
  frequency := n • V.frequency
  height i := by
    simpa only [LinearMap.smul_apply, nsmul_eq_mul] using rationalLogHeight_nat_mul n (V.height i)
  vertical a z hz x := by
    simp only [V.vertical _ z hz x, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, realifyFunctional_nsmul, AddCircle.coe_nsmul, character_nsmul]
  integral z hz hL := by
    obtain ⟨m, hm⟩ := V.integral z hz hL
    refine ⟨(n : ℤ) * m, ?_⟩
    rw [realifyFunctional_nsmul, hm]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

noncomputable def reindex {J : Type*} [Fintype J]
    (V : D.UnitVerticalObservable T I p) (e : I ≃ J) : D.UnitVerticalObservable T J p where
  observable j := V.observable (e.symm j)
  unit x := (e.symm.sum_comp (fun i => ‖V.observable i x‖ ^ 2)).trans (V.unit x)
  norm j := V.norm (e.symm j)
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := fun j => V.lipschitz (e.symm j)
  frequency := V.frequency
  height := V.height
  vertical j := V.vertical (e.symm j)
  integral := V.integral

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

theorem exists_of_unit_data {σ I : Type*} {L : Type}
    [Fintype σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
    (M : D.MultidegreeStructure bound) (hstep : t = ∑ i, bound i)
    {p : ℝ} (hM : M.ComplexityLE p)
    (g : M.filtration.realification.PolynomialOrbit)
    (V : D.UnitVerticalObservable (D.filtration.realification.subgroup t) I p)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) :
    ∃ W : NativeMultidegreeNilcharacter bound p, ∃ e : I ≃ Fin W.outputDim,
      W.dim = d ∧ ∀ i x, W.eval (e i) x = V.observable i
        (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) := by
  classical
  subst hstep
  let V' : D.UnitVerticalObservable (M.realSubgroup bound) I p :=
    { V with
      vertical := fun i z hz x => V.vertical i z (M.realSubgroup_top ▸ hz) x
      integral := fun z hz hL => V.integral z (M.realSubgroup_top ▸ hz) hL }
  obtain ⟨i, _⟩ := exists_large_unit_coordinate
    (fun i => V.observable i (QuotientGroup.mk 1)) (V.unit _)
  let W : NativeMultidegreeNilcharacter bound p :=
    { L := L
      dim := d
      model := D
      multi := M
      complexity := hM
      orbit := g
      outputDim := Fintype.card I
      output_pos := Fintype.card_pos_iff.mpr ⟨i⟩
      output_bound := hI
      vertical := V'.reindex (Fintype.equivFin I) }
  refine ⟨W, Fintype.equivFin I, rfl, ?_⟩
  intro i x
  change V.observable ((Fintype.equivFin I).symm ((Fintype.equivFin I) i)) _ = _
  rw [Equiv.symm_apply_apply]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def tensorIndexEquiv (d n : ℕ) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_fun, Fintype.card_fin])

noncomputable def tensorPowerBudget (n : ℕ) (p : ℝ) : ℝ := (n + 1) * (p + 1)

theorem tensorPowerBudget_bounds (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ tensorPowerBudget n p ∧ p + n + 1 ≤ tensorPowerBudget n p ∧
      (n : ℝ) * p ≤ tensorPowerBudget n p := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  unfold tensorPowerBudget
  constructor
  · nlinarith [mul_nonneg hn hp]
  constructor <;> nlinarith [mul_nonneg hn hp]

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def tensorPower (n : ℕ) : NativeMultidegreeNilcharacter bound (tensorPowerBudget n p) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hb := tensorPowerBudget_bounds n hp
  exact {
    L := W.L
    dim := W.dim
    model := W.model
    multi := W.multi
    complexity := W.complexity.mono W.multi hb.1
    orbit := W.orbit
    outputDim := W.outputDim ^ n
    output_pos := pow_pos W.output_pos n
    output_bound := by
      simpa only [Nat.cast_pow] using
        (pow_le_pow_left₀ (Nat.cast_nonneg W.outputDim) W.output_bound n).trans
          (by rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hb.2.2)
    vertical := ((W.vertical.tensorPower n).reindex (tensorIndexEquiv W.outputDim n)).mono hb.2.1 }

theorem tensorPower_eval (n : ℕ) (a : Fin (W.outputDim ^ n)) (x : σ → ℤ) :
    (W.tensorPower n).eval a x = ∏ j, W.eval ((tensorIndexEquiv W.outputDim n).symm a j) x := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def tensorVector {σ I : Type*} (f : I → (σ → ℤ) → ℂ)
    (n : ℕ) (a : Fin n → I) (x : σ → ℤ) : ℂ := ∏ j, f (a j) x

theorem product_flatten {q n N : ℕ} (e : (Fin q × Fin n) ≃ Fin N)
    (f : Fin q → Fin n → ℂ) :
    (∏ i, ∏ j, f i j) = ∏ k, f (e.symm k).1 (e.symm k).2 := by
  calc
    _ = ∏ a : Fin q × Fin n, f a.1 a.2 := (Fintype.prod_prod_type (fun a => f a.1 a.2)).symm
    _ = _ := (e.symm.prod_comp (fun a => f a.1 a.2)).symm

noncomputable def rootTensorEquiv (q t : ℕ) (ht : 1 ≤ t) :
    (Fin q × Fin (q ^ (t - 1))) ≃ Fin (((q : ℤ) ^ t).natAbs) :=
  finProdFinEquiv.trans (finCongr (by
    have h : q * q ^ (t - 1) = q ^ t := by rw [← pow_succ', Nat.sub_add_cancel ht]
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h))

noncomputable def rootTensorIndex (d q t : ℕ) (ht : 1 ≤ t)
    (a : Fin q → Fin (d ^ (q ^ (t - 1)))) : Fin (((q : ℤ) ^ t).natAbs) → Fin d :=
  fun k => (tensorIndexEquiv d (q ^ (t - 1))).symm
    (a ((rootTensorEquiv q t ht).symm k).1) ((rootTensorEquiv q t ht).symm k).2

theorem NativeMultidegreeNilcharacter.tensorPower_tensor_eval
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (q t : ℕ) (ht : 1 ≤ t)
    (a : Fin q → Fin (W.outputDim ^ (q ^ (t - 1)))) (x : σ → ℤ) :
    tensorVector (W.tensorPower (q ^ (t - 1))).eval q a x =
      signedTensorVector W.eval ((q : ℤ) ^ t) (rootTensorIndex W.outputDim q t ht a) x := by
  unfold tensorVector
  simp_rw [W.tensorPower_eval]
  have hnonneg : 0 ≤ (q : ℤ) ^ t := pow_nonneg (Int.natCast_nonneg q) _
  simp only [signedTensorVector, signedTensorProduct, ite_eq_right (not_lt.mpr hnonneg)]
  exact product_flatten (rootTensorEquiv q t ht) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem tensorVector_unit {σ I : Type*} [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (n : ℕ) (x : σ → ℤ) :
    ∑ a : Fin n → I, ‖tensorVector f n a x‖ ^ 2 = 1 := by
  simp only [tensorVector, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ _j : Fin n, ∑ i : I, ‖f i x‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [hunit, Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

structure SymmetricSquarefreeUnitData (p : ℝ) (η : L →ₗ[ℚ] ℚ) (q : ℝ) where
  grid : ℕ
  grid_pos : 0 < grid
  stable : M.SquarefreeGridStable p grid
  complexity : (M.squarefreeModelMultidegree p grid grid_pos stable).ComplexityLE q
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  observable : (M.squarefreeModel p grid grid_pos stable).UnitVerticalObservable
    ((M.squarefreeModel p grid grid_pos stable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound)))
    (SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin coordinateCount)) q
  frequency : observable.frequency = M.filtration.replicatedFrequency η
  invariant : ∀ (e : ReplicatedPermutation bound) k x,
    observable.observable k (M.squarefreeSpacePermute p grid grid_pos stable e x) =
      observable.observable k x
  dimension :
    (Fintype.card (SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound))
      (Fin coordinateCount)) : ℝ) ≤ Real.exp q

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)

noncomputable def comparisonVerticalProduct (ε : D.RealGroup)
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : E.Space) : ℂ :=
  (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x) *
  star (U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x))

theorem comparisonVerticalProduct_norm (ε : D.RealGroup)
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : E.Space) : ‖M.comparisonVerticalProduct V U E hEL ε a k x‖ ≤ 1 := by
  unfold comparisonVerticalProduct
  rw [norm_mul, norm_star]
  simpa only [mul_one] using mul_le_mul
    ((V.tensorPower (multidegreeFactorial bound)).norm a _) (U.observable.norm k _)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators

theorem exists_controlled_symmetric_squarefree_unit (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound), (∑ i, bound i) = t →
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        {p : ℝ}, M.ComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      Nonempty (M.SymmetricSquarefreeUnitData (p + t.factorial + 1) η ((p + C) ^ C)) := by
  obtain ⟨a, _, hinvariant⟩ := exists_prescribed_invariant_unit t t.factorial
  obtain ⟨b, _, hfrequency⟩ := exists_squarefreeFrequency_cost t
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + Polynomial.C t.factorial + 1
  let R := (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ s d D bound M ht _ _ _ _ p hM η hη
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let q := p + t.factorial + 1
  let m := Fintype.card (ReplicatedPermutation bound)
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨1⟩
  have hmle : m ≤ t.factorial := by
    simpa only [ht] using replicatedPermutation_card_le bound
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) t.factorial]
  have hηdiv (i) : rationalLogHeight (dividedFrequency m η (D.basis i)) ≤ q := by
    apply (dividedFrequency_height m hm η (D.basis i) (hη i)).trans
    have hmr : (m : ℝ) ≤ t.factorial := by exact_mod_cast hmle
    dsimp [q]
    linarith
  obtain ⟨B, hB, hstable, hE, hηE, hint⟩ :=
    M.exists_controlled_replicated_frequency (hM.mono M hpq) (dividedFrequency m η) hηdiv
  rw [ht] at hE hηE
  let r := (q + b) ^ b
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : squarefreeFrequencyModelBudget t q ≤ r := hfrequency q hq
  have hEr := hE.mono (M.squarefreeModelMultidegree q B hB hstable) hqr
  let E := M.squarefreeModel q B hB hstable
  let := M.squarefreeSpaceAction q B hB hstable
  have hstep : Fintype.card (ReplicatedIndex bound) = t := (replicatedIndex_card bound).trans ht
  rw [← hstep] at hinvariant
  obtain ⟨n, hn, hdim, W, hW, hWinv⟩ := hinvariant (Γ := ReplicatedPermutation bound) E
    (by simpa only [hstep] using hmle) hr hEr.1
    (fun e => M.squarefreeSpacePermute_lipschitz q B hB hstable hr hEr.1 e)
    (fun e z hz x => M.squarefreeSpacePermute_commutes_top q B hB hstable e z hz x)
    (M.filtration.replicatedFrequency (dividedFrequency m η)) (fun i => (hηE i).trans hqr) hint
  have htotal : q + r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, R, X, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hra : 0 ≤ (r + a) ^ a := by positivity
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hWC : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  refine ⟨{
    grid := B
    grid_pos := hB
    stable := hstable
    complexity := hEr.mono (M.squarefreeModelMultidegree q B hB hstable) hrC
    coordinateCount := n
    coordinateCount_pos := hn
    observable := W.mono hWC
    frequency := ?_
    invariant := hWinv
    dimension := hdim.trans (Real.exp_le_exp.mpr hWC) }⟩
  change W.frequency = M.filtration.replicatedFrequency η
  rw [hW]
  ext x
  simp only [LinearMap.smul_apply, nsmul_eq_mul, MultidegreeLieFiltration.replicatedFrequency_apply,
    dividedFrequency, smul_eq_mul]
  change (m : ℚ) * ((m : ℚ)⁻¹ * η _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_mul]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (U : M.SymmetricSquarefreeUnitData p η q)

noncomputable def eval (g : M.filtration.realification.PolynomialOrbit)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) : ℂ :=
  U.observable.observable k (QuotientGroup.mk
    ((M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).realification.polynomialOrbitEval
      x (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g)))

theorem eval_permute (g : M.filtration.realification.PolynomialOrbit)
    (e : ReplicatedPermutation bound)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) :
    U.eval g k (fun j => x ((replicatedPermutation bound e).symm j)) = U.eval g k x := by
  unfold eval
  rw [← M.filtration.polarizeRealOrbit_permute (fun j : ReplicatedIndex bound => j.1)
    g (replicatedPermutation bound e) (replicatedPermutation_block bound e) x]
  change U.observable.observable k (QuotientGroup.mk
    (M.squarefreeRealPermute p U.grid U.grid_pos U.stable e _)) = _
  rw [← M.squarefreeSpacePermute_mk]
  exact U.invariant e k _

theorem unit_eval (g : M.filtration.realification.PolynomialOrbit)
    (x : ReplicatedIndex bound → ℤ) : ∑ k, ‖U.eval g k x‖ ^ 2 = 1 :=
  U.observable.unit _

theorem norm_eval (g : M.filtration.realification.PolynomialOrbit)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) : ‖U.eval g k x‖ ≤ 1 := U.observable.norm k _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q r : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

noncomputable def mono (U : M.SymmetricSquarefreeUnitData p η q) (hqr : q ≤ r) :
    M.SymmetricSquarefreeUnitData p η r := {
  U with
  complexity := U.complexity.mono _ hqr
  observable := U.observable.mono hqr
  dimension := U.dimension.trans (Real.exp_le_exp.mpr hqr) }

theorem mono_eval (U : M.SymmetricSquarefreeUnitData p η q) (hqr : q ≤ r)
    (g : M.filtration.realification.PolynomialOrbit)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) : (U.mono hqr).eval g k x = U.eval g k x := rfl

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

end OAI
