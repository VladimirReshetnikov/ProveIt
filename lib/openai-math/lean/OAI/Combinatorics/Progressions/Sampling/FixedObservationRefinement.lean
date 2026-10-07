/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeProductPartition
import OAI.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
import OAI.Combinatorics.Progressions.Estimates.TranslatedShiftTesting

namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type v} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{max u v} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x))
               ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => y)) ≤ ρ) := by
  obtain ⟨C, hC, hpartition⟩ := exists_native_product_partition s a
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ d D g N _ p ρ hp hι hD hρ hρinv
  let G := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) g
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) hp hι hD hρ hρinv G
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      ((pi D).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  have hpoint (i : ι) (x : ZMod N) :
      productProjection D i ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x)) =
        (D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x) := by
    exact congrArg (fun z : (D i).RealGroup => (QuotientGroup.mk z : (D i).Space))
      (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) g
        (fun _ : Unit => (x.val : ℤ)) i)
  refine ⟨n, hn, hnb, A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test (pi D) le_rfl (tests j) (hunit j) (hcomplexity j) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x))
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy) i
    simpa only [hpoint] using hd

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_shifted_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_observation_partition.{0, 0} s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * X + 3 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g N _ p ρ hp hι hD hρ hρinv
  let E := fun k : ι × Fin 3 => D k.1
  let G := fun k : ι × Fin 3 =>
    (g k.1).translate (fun _ => Nat.zero_lt_one) (fun _ => ((k.2.val : ℤ) - 1) * N)
  let : FiniteDimensional ℚ (∀ k : ι × Fin 3, L k.1) :=
    (productFinBasis E).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1)) :=
    realification_moduleTopology_t2 (productFinBasis E)
  let r := 3 * p + 3
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcount : (Fintype.card (ι × Fin 3) : ℝ) ≤ r := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hinv : 1 / ρ ≤ Real.exp ((r + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ :=
    hpartition E G N hr hcount (fun k => (hD k.1).mono (D k.1) hpr) hρ hinv
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  intro j x y hx hy i t ht
  have ht' := abs_le.mp ht
  let k : Fin 3 := ⟨(t + 1).toNat, by omega⟩
  have hk : (k.val : ℤ) - 1 = t := by dsimp [k]; omega
  simpa only [E, G, cyclicOrbitPoint_translate, hk] using hdiam j x y hx hy (i, k)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_observation_refinement (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι I : Type} [Fintype ι] [DecidableEq ι] [Fintype I]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      {degree N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) {p ρ : ℝ},
      s ≤ degree → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      (∀ j, PositiveCyclicNiltest.{0} degree N p (A j)) → (∀ x, ∑ j, A j x = 1) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (I × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (I × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → 0 < A j.1 x) ∧
          (∀ (h : ZMod N) j k x, 0 < U j x * U k (x + h) →
            0 < A j.1 x * A k.1 (x + h)) ∧
          letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
          ∀ j x y, 0 < U j x → 0 < U j y → ∀ i,
            dist ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x))
              ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => y)) ≤ ρ := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_observation_partition s a
  let X : Polynomial ℕ := Polynomial.X
  let V := X + (X + Polynomial.C B) ^ B
  let R := V + (V + 2) ^ 2 + 3
  let P := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + P)
  refine ⟨C, hC, ?_⟩
  intro ι I _ _ _ L _ _ _ _ _ _ d D g degree N _ A p ρ hs hp hι hD hcard hA hsum hρ hρinv
  let : FiniteDimensional ℚ (∀ i, L i) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) := realification_moduleTopology_t2 (productFinBasis D)
  obtain ⟨n, hn, hnb, W, hW, hWsum, hWdiam⟩ := hpartition D g N hp hι hD hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [X, V, R, P, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hP : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right hP).trans hcost
  have hPC : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let U : (I × Fin n) → ZMod N → ℝ := fun j x => A j.1 x * W j.2 x
  have hpositive j x (hx : 0 < U j x) : 0 < A j.1 x ∧ 0 < W j.2 x := by
    change 0 < A j.1 x * W j.2 x at hx
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hA j.1).unit_interval x).1]
  have hU j : PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j) :=
    (((hA j.1).mono le_rfl hpt).mul ((hW j.2).mono hs hBt) ht).mono le_rfl hPC
  refine ⟨n, hn, ?_, U, hU, ?_, fun j x hx => (hpositive j x hx).1, ?_, ?_⟩
  · calc
      _ = (Fintype.card I : ℝ) * n := by rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      _ ≤ Real.exp p * Real.exp ((p + B) ^ B) :=
        mul_le_mul hcard hnb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp t := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr htC
  · intro x
    simp only [U, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hWsum, mul_one]
    exact hsum x
  · intro h j k x hx
    have hpos : 0 < U j x ∧ 0 < U k (x + h) := by
      rcases mul_pos_iff.mp hx with h | h
      · exact h
      · linarith [((hU j).unit_interval x).1]
    exact mul_pos (hpositive j x hpos.1).1 (hpositive k (x + h) hpos.2).1
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i
    exact hWdiam j.2 x y (hpositive j x hx).2 (hpositive j y hy).2 i

end Erdos3.RationalFilteredNilmanifold

end

end OAI
