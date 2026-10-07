import OAI.Combinatorics.Progressions.Nilpotent.NativeResidueNiltests
import OAI.Combinatorics.Progressions.Sampling.FixedObservationRefinement

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residue_indicator_positiveCyclicNiltest {q N : ℕ} [NeZero q] [NeZero N]
    (j : ZMod q) {p : ℝ} (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    PositiveCyclicNiltest.{0} 1 N (p + 2)
      (fun x => if (x.val : ZMod q) = j then 1 else 0) := by
  classical
  refine .of_test (RationalTorus.nilmanifold 1) le_rfl (RationalTorus.residueNiltest j)
    (RationalTorus.residueNiltest_unit_interval j) (RationalTorus.residueNiltest_complexity j hp hq) ?_
  intro x
  rw [RationalTorus.residueNiltest_evalCyclic]
  split_ifs <;> rfl

theorem refine_positive_partition_by_residue {I : Type*} [Fintype I]
    {degree q N : ℕ} [NeZero q] [NeZero N] (A : I → ZMod N → ℝ) {p : ℝ}
    (hp : 0 ≤ p) (hdegree : 1 ≤ degree) (hq : (q : ℝ) ≤ Real.exp p)
    (hA : ∀ i, PositiveCyclicNiltest.{0} degree N p (A i)) (hsum : ∀ x, ∑ i, A i x = 1) :
    ∃ B : (I × ZMod q) → ZMod N → ℝ,
      (∀ j, PositiveCyclicNiltest.{0} degree N
        (productNiltestBudget (raisedNiltestBudget (p + 2))) (B j)) ∧
      (∀ x, ∑ j, B j x = 1) ∧
      (∀ j x, 0 < B j x → 0 < A j.1 x ∧ (x.val : ZMod q) = j.2) := by
  classical
  let B : (I × ZMod q) → ZMod N → ℝ := fun j x =>
    A j.1 x * if (x.val : ZMod q) = j.2 then 1 else 0
  refine ⟨B, ?_, ?_, ?_⟩
  · intro j
    exact ((hA j.1).mono le_rfl (by linarith)).mul
      ((residue_indicator_positiveCyclicNiltest j.2 hp hq).mono hdegree le_rfl) (by linarith)
  · intro x
    simpa [B, Fintype.sum_prod_type, mul_ite] using hsum x
  · intro j x hx
    by_cases h : (x.val : ZMod q) = j.2
    · exact ⟨by simpa only [B, h, ↓reduceIte, mul_one] using hx, h⟩
    · simp only [B, h, ↓reduceIte, mul_zero, lt_self_iff_false] at hx

theorem exists_controlled_residue_refinement :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I]
      {degree q N : ℕ} [NeZero q] [NeZero N] (A : I → ZMod N → ℝ) {p : ℝ},
      0 ≤ p → 1 ≤ degree → (Fintype.card I : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      (∀ i, PositiveCyclicNiltest.{0} degree N p (A i)) → (∀ x, ∑ i, A i x = 1) →
      ∃ B : (I × ZMod q) → ZMod N → ℝ,
        (Fintype.card (I × ZMod q) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (B j)) ∧
        (∀ x, ∑ j, B j x = 1) ∧
        ∀ j x, 0 < B j x → 0 < A j.1 x ∧ (x.val : ZMod q) = j.2 := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 2) + (X + 4) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + Q)
  refine ⟨C, hC, ?_⟩
  intro I _ degree q N _ _ A p hp hdegree hcard hq hA hsum
  obtain ⟨B, hB, hBsum, hsupport⟩ := refine_positive_partition_by_residue A hp hdegree hq hA hsum
  have hcost : 2 * p + productNiltestBudget (raisedNiltestBudget (p + 2)) ≤ (p + C) ^ C := by
    simpa [X, Q, R, Polynomial.eval₂_pow, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, show p + 2 + 2 = p + 4 by ring] using hbudget p hp
  have hnonneg : 0 ≤ productNiltestBudget (raisedNiltestBudget (p + 2)) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  refine ⟨B, ?_, fun j => (hB j).mono le_rfl (by linarith), hBsum, hsupport⟩
  calc
    _ = (Fintype.card I : ℝ) * q := by rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
    _ ≤ Real.exp p * Real.exp p := mul_le_mul hcard hq (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_observation_residue_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ ((n * q : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod q) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.2) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x))
               ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => y)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_observation_partition.{0, 0} s a
  obtain ⟨R, _, hrefine⟩ := exists_controlled_residue_refinement
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ := hpartition D g N hp hι hD hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  obtain ⟨U, hcount, hU, hUsum, hsupport⟩ := hrefine (q := q) A ht hs
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hBt))
    (hq.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hA j).mono le_rfl hBt) hsum
  have hsumcost : t + (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsumcost
  refine ⟨n, hn, ?_, U, fun j => (hU j).mono le_rfl hcost, hUsum,
    fun j x hx => (hsupport j x hx).2, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card] using
      hcount.trans (Real.exp_le_exp.mpr hcost)
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i
    exact hdiam j.1 x y (hsupport j x hx).1 (hsupport j y hy).1 i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_shifted_residue_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ ((n * q : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod q) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.2) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_shifted_observation_partition s a
  obtain ⟨R, _, hrefine⟩ := exists_controlled_residue_refinement
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ := hpartition D g N hp hι hD hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  obtain ⟨U, hcount, hU, hUsum, hsupport⟩ := hrefine (q := q) A ht hs
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hBt))
    (hq.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hA j).mono le_rfl hBt) hsum
  have hsumcost : t + (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsumcost
  refine ⟨n, hn, ?_, U, fun j => (hU j).mono le_rfl hcost, hUsum,
    fun j x hx => (hsupport j x hx).2, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card] using
      hcount.trans (Real.exp_le_exp.mpr hcost)
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i t ht
    exact hdiam j.1 x y (hsupport j x hx).1 (hsupport j y hy).1 i t ht

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_interval_residue_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N M : ℕ) [NeZero N] [NeZero M] {p ρ : ℝ},
      0 ≤ p → (M : ℝ) ≤ Real.exp p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (Fin n × ZMod M) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod M) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, x ∉ cyclicWrapExceptional 0 ρ → y ∉ cyclicWrapExceptional 0 ρ →
            0 < A j x → 0 < A j y →
            |(x.val : ℝ) - y.val| ≤ N * ρ ∧ (M : ℤ) ∣ (x.val : ℤ) - y.val := by
  obtain ⟨b, _, hpart⟩ := exists_interval_circle_partition a
  obtain ⟨c, _, hrefine⟩ := exists_controlled_residue_refinement
  let B : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N M _ _ p ρ hp hM hρ hprec
  classical
  obtain ⟨n, hn, hnb, V, hV, hsum, hdiam⟩ := hpart N hp hρ hprec
  let t := p + (p + b) ^ b
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hbt : (p + b) ^ b ≤ t := le_add_of_nonneg_left hp
  have hcost : (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, t, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, hcard, hA, hAsum, hsupport⟩ := hrefine V (hp.trans hpt) le_rfl
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hbt))
    (hM.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hV j).mono le_rfl hbt) hsum
  refine ⟨n, hn, hcard.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hAsum, ?_⟩
  intro j x y hx hy hAx hAy
  obtain ⟨hVx, hMx⟩ := hsupport j x hAx
  obtain ⟨hVy, hMy⟩ := hsupport j y hAy
  have hnear := good_circle_observations_control_representatives 0 x y hρ hx hy
    (hdiam j.1 x y hVx hVy)
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [← sub_div, abs_div, abs_of_pos hN] at hnear
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hN).mp hnear, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((x.val : ℤ) - y.val) M).mp
  push_cast
  rw [hMx, hMy, sub_self]

end Erdos3

end

end OAI
