import OAI.Combinatorics.Progressions.Geometry.NativeIntervalCoordinate
import OAI.Combinatorics.Progressions.Nilpotent.NativeNiltestPartition
import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

universe u

section

namespace Erdos3

theorem exists_cyclic_partition_offsets {I : Type*} {N : ℕ} [NeZero N]
    (A : I → ZMod N → ℝ) (h : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hdiam : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ∃ b : I → ℤ, ∀ i x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
      ((h + x).val : ℤ) = (x.val : ℤ) + b i := by
  classical
  have hlocal (i : I) : ∃ b : ℤ, ∀ x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
      ((h + x).val : ℤ) = (x.val : ℤ) + b := by
    by_cases hex : ∃ y, y ∉ cyclicWrapExceptional h ρ ∧ 0 < A i y
    · obtain ⟨y, hy, hAy⟩ := hex
      refine ⟨((h + y).val : ℤ) - (y.val : ℤ), ?_⟩
      intro x hx hAx
      have he := cyclic_representative_difference_of_good_circle h x y hρ hx hy
        (hdiam i x y hAx hAy)
      linarith
    · exact ⟨0, fun x hx hAx => False.elim (hex ⟨x, hx, hAx⟩)⟩
  choose b hb using hlocal
  exact ⟨b, hb⟩

end Erdos3

end

section

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct BigOperators

theorem mul {degree N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f)
    (hg : PositiveCyclicNiltest.{u} degree N p g) (hp : 0 ≤ p) :
    PositiveCyclicNiltest.{u} degree N (productNiltestBudget (raisedNiltestBudget p))
      (fun x => f x * g x) := by
  rcases hf with @⟨L₁, lie₁, alg₁, s₁, dim₁, top₁, add₁, smul₁, t2₁, D₁, hs₁, A, hA, hAc, hevalA⟩
  rcases hg with @⟨L₂, lie₂, alg₂, s₂, dim₂, top₂, add₂, smul₂, t2₂, D₂, hs₂, B, hB, hBc, hevalB⟩
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep hs₂
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact B.raiseStep hs₂
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget p) := by
    intro b
    cases b
    · exact B.raiseStep_complexity hs₂ hp hBc
    · exact A.raiseStep_complexity hs₁ hp hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact B.raiseStep_unit_interval hs₂ hB
    · exact A.raiseStep_unit_interval hs₁ hA
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget p := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc
  have hSc := RationalFilteredNilmanifold.piNiltest_complexity D U hp' hcard hUc
  have hSu := RationalFilteredNilmanifold.piNiltest_unit_interval D U hp' hcard hUc hU
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * B.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (B.raiseStep hs₂).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  refine .of_test (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc ?_
  intro x
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (B.unit_interval_evalCyclic hB N (fun _ => x)).1, zero_mul, sub_zero, hevalA x, hevalB x]

end Erdos3.PositiveCyclicNiltest

end

section

namespace Erdos3

open scoped TensorProduct

theorem exists_interval_circle_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ := by
  obtain ⟨B, _, hpartition⟩ := RationalFilteredNilmanifold.exists_native_niltest_partition 1 a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p ρ hp hρ hρinv
  let D := RationalTorus.nilmanifold 1
  let G := RationalTorus.intervalOrbit N
  have hD : D.GeometryComplexityLE (p + 1) :=
    RationalTorus.nilmanifold_geometry 1 (by linarith) (by norm_num; linarith)
  have hρinv' : 1 / ρ ≤ Real.exp (((p + 1) + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) _))
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) (by linarith) hD hρ hρinv' G
  have hcost : (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable (D.cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test D le_rfl (tests j) (hunit j) ((hcomplexity j).mono hcost) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum (D.cyclicOrbitPoint G N (fun _ : Unit => x))
  · let := D.metricSpace
    intro j x y hx hy
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy)
    have hp := RationalTorus.intervalCoordinate_lipschitz.dist_le_mul
      (D.cyclicOrbitPoint G N (fun _ : Unit => x)) (D.cyclicOrbitPoint G N (fun _ : Unit => y))
    change dist (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => x)) 0)
      (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => y)) 0) ≤
      (1 : ℝ) * dist (D.cyclicOrbitPoint G N (fun _ : Unit => x))
        (D.cyclicOrbitPoint G N (fun _ : Unit => y)) at hp
    rw [RationalTorus.intervalOrbit_phase, RationalTorus.intervalOrbit_phase, one_mul] at hp
    exact hp.trans hd

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_positive_translation_partition {I : Type*} [Fintype I]
    {degree N : ℕ} [NeZero N] {p ρ : ℝ} (hp : 0 ≤ p) (hρ : 0 < ρ)
    (f : ZMod N → ℝ) (hf : PositiveCyclicNiltest.{0} degree N p f)
    (A : I → ZMod N → ℝ) (hA : ∀ i, PositiveCyclicNiltest.{0} degree N p (A i))
    (hsum : ∀ x, ∑ i, A i x = 1)
    (hdiam : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) (h : ZMod N) :
    ∃ U : I → ZMod N → ℝ,
      (∀ i, PositiveCyclicNiltest.{0} degree N
        (productNiltestBudget (raisedNiltestBudget p)) (U i)) ∧
      (∀ x, 0 ≤ ∑ i, U i x ∧ ∑ i, U i x ≤ 1) ∧
      (∀ x, x ∉ cyclicWrapExceptional h ρ → f (h + x) = ∑ i, U i x) ∧
      (𝔼 x, |f (h + x) - ∑ i, U i x|) ≤ 6 * ρ + 3 / N := by
  classical
  have hfunit (x) := hf.unit_interval x
  obtain ⟨b, hb⟩ := exists_cyclic_partition_offsets A h hρ hdiam
  rcases hf with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  let g : I → ZMod N → ℝ := fun i x => (T.eval (fun _ => (x.val : ℤ) + b i)).re
  have hg (i) : PositiveCyclicNiltest.{0} degree N p (g i) := by
    refine .of_test D hs (T.translate (fun _ => Nat.zero_lt_one) (fun _ => b i)) hT hTc ?_
    intro x
    simp only [g, RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_translate]
    rfl
  let U : I → ZMod N → ℝ := fun i x => A i x * g i x
  have hgood (x) (hx : x ∉ cyclicWrapExceptional h ρ) : f (h + x) = ∑ i, U i x := by
    have heach (i) : A i x * g i x = A i x * f (h + x) := by
      by_cases hzero : A i x = 0
      · simp only [hzero, zero_mul]
      · have hpos : 0 < A i x := lt_of_le_of_ne ((hA i).unit_interval x).1 (Ne.symm hzero)
        have he : g i x = f (h + x) := by
          rw [heval]
          change (T.eval (fun _ => (x.val : ℤ) + b i)).re =
            (T.eval (fun _ => ((h + x).val : ℤ))).re
          rw [hb i x hx hpos]
        rw [he]
    simp only [U, heach, ← Finset.sum_mul, hsum, one_mul]
  refine ⟨U, fun i => (hA i).mul (hg i) hp, ?_, hgood, ?_⟩
  · intro x
    exact positive_partition_sum_unit_interval (fun i => A i x) (fun i => g i x)
      (fun i => ((hA i).unit_interval x).1) (hsum x) (fun i => (hg i).unit_interval x)
  · have hm := positive_partition_approximation_mean_error (cyclicWrapExceptional h ρ)
      A g (fun x => f (h + x)) (by norm_num : (0 : ℝ) ≤ 0)
      (fun i x => ((hA i).unit_interval x).1) hsum
      (fun i x => (hg i).unit_interval x) (fun x => hfunit (h + x))
      (fun x hx => by
        change |f (h + x) - ∑ i, U i x| ≤ 0
        simp only [← hgood x hx, sub_self, abs_zero, le_refl])
    have hm' : (𝔼 x, |f (h + x) - ∑ i, U i x|) ≤
        ((cyclicWrapExceptional h ρ).card : ℝ) / N := by
      simpa only [U, zero_add, ZMod.card] using hm
    exact hm'.trans (cyclicWrapExceptional_density_le h hρ.le)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_interval_refined_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] {s N : ℕ} [NeZero N]
      (A : I → ZMod N → ℝ) {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p →
      (∀ i, PositiveCyclicNiltest.{0} s N p (A i)) → (∀ x, ∑ i, A i x = 1) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (I × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (I × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → 0 < A j.1 x) ∧
          (∀ j x y, 0 < U j x → 0 < U j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          ∀ h j x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
            0 < U j x → 0 < U j y →
            |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ ∧
              (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) ∧
              ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  obtain ⟨B, _, hinterval⟩ := exists_interval_circle_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let R := T + (T + 2) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * T + Q)
  refine ⟨C, hC, ?_⟩
  intro I _ s N _ A p ρ hs hp hcard hA hsum hρ hρinv
  obtain ⟨n, hn, hnb, V, hV, hVsum, hdiam⟩ := hinterval N hp hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : 2 * t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [T, X, R, Q, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hQ0 : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  let U : (I × Fin n) → ZMod N → ℝ := fun j x => A j.1 x * V j.2 x
  have hpositive (j : I × Fin n) (x : ZMod N) (hx : 0 < U j x) :
      0 < A j.1 x ∧ 0 < V j.2 x := by
    change 0 < A j.1 x * V j.2 x at hx
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hA j.1).unit_interval x).1]
  refine ⟨n, hn, ?_, U, ?_, ?_, fun j x hx => (hpositive j x hx).1,
    fun j x y hx hy => hdiam j.2 x y (hpositive j x hx).2 (hpositive j y hy).2,
    fun h => cyclicWrapExceptional_density_le h hρ.le, ?_⟩
  · calc
      _ = (Fintype.card I : ℝ) * n := by rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      _ ≤ Real.exp p * Real.exp ((p + B) ^ B) :=
        mul_le_mul hcard hnb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp t := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr htC
  · intro j
    exact (((hA j.1).mono le_rfl hpt).mul ((hV j.2).mono hs hBt) ht).mono le_rfl hproduct
  · intro x
    simp only [U, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hVsum, mul_one]
    exact hsum x
  · intro h j x y hx hy hUx hUy
    have hxy := hdiam j.2 x y (hpositive j x hUx).2 (hpositive j y hUy).2
    exact ⟨good_circle_observations_control_representatives h x y hρ hx hy hxy,
      cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hxy,
      cyclic_representative_difference_of_good_circle h x y hρ hx hy hxy⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem PositiveCyclicNiltest.eq_of_degree_zero {N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} 0 N p f) (x y : ZMod N) :
    f x = f y := by
  rcases hf with ⟨D, hs, T, _, _, heval⟩
  have hz : _ = 0 := Nat.eq_zero_of_le_zero hs
  subst hz
  rw [heval x, heval y]
  exact congrArg Complex.re ((RationalFilteredNilmanifold.Niltest.eval_step_zero D T _).trans
    (RationalFilteredNilmanifold.Niltest.eval_step_zero D T _).symm)

theorem exists_positive_cyclic_translation_approximation (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p ρ : ℝ},
      0 ≤ p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} s N p f → ∀ h : ZMod N,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : Fin n → ZMod N → ℝ,
          (∀ i, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (U i)) ∧
          (∀ x, 0 ≤ ∑ i, U i x ∧ ∑ i, U i x ≤ 1) ∧
          (∀ x, x ∉ cyclicWrapExceptional h ρ → f (h + x) = ∑ i, U i x) ∧
          (𝔼 x, |f (h + x) - ∑ i, U i x|) ≤ 6 * ρ + 3 / N := by
  obtain ⟨B, _, hinterval⟩ := exists_interval_circle_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let R := T + (T + 2) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * T + Q)
  refine ⟨C, hC, ?_⟩
  intro s N _ p ρ hp hρ hρinv f hf h
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : 2 * t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [T, X, R, Q, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hQ0 : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  cases s with
  | zero =>
    refine ⟨1, by norm_num, ?_, fun _ => f, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (ht.trans htC)
    · intro i
      exact hf.mono le_rfl (hpt.trans htC)
    · intro x
      simpa using hf.unit_interval x
    · intro x _
      simpa using hf.eq_of_degree_zero (h + x) x
    · have he (x) : f (h + x) = f x := hf.eq_of_degree_zero _ _
      simpa [he] using (show (0 : ℝ) ≤ 6 * ρ + 3 / N by positivity)
  | succ s =>
    obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ := hinterval N hp hρ hρinv
    obtain ⟨U, hU, hrange, hgood, hmean⟩ := exists_positive_translation_partition ht hρ f
      (hf.mono le_rfl hpt) A (fun i => (hA i).mono (by omega) hBt) hsum hdiam h
    exact ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr (hBt.trans htC)), U,
      fun i => (hU i).mono le_rfl hproduct, hrange, hgood, hmean⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_weighted_sum_approximation_le {X I : Type*} [Fintype X] [Fintype I]
    (w f : X → ℝ) (U : I → X → ℝ) {M delta error : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, |w x| ≤ M) (happrox : (𝔼 x, |f x - ∑ i, U i x|) ≤ delta)
    (hpiece : ∀ i, (𝔼 x, w x * U i x) ≤ error) :
    (𝔼 x, w x * f x) ≤ (Fintype.card I : ℝ) * error + M * delta := by
  have hpoint (x) : w x * f x ≤ (∑ i, w x * U i x) + M * |f x - ∑ i, U i x| := by
    have he : w x * (f x - ∑ i, U i x) ≤ M * |f x - ∑ i, U i x| := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hw x) (abs_nonneg _)
    rw [← Finset.mul_sum]
    nlinarith
  calc
    _ ≤ (𝔼 x, ((∑ i, w x * U i x) + M * |f x - ∑ i, U i x|)) :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = (∑ i, 𝔼 x, w x * U i x) + M * (𝔼 x, |f x - ∑ i, U i x|) := by
      rw [Finset.expect_add_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
    _ ≤ (Fintype.card I : ℝ) * error + M * delta := by
      apply add_le_add
      · calc
          _ ≤ ∑ _i : I, error := Finset.sum_le_sum (fun i _ => hpiece i)
          _ = _ := by simp
      · exact mul_le_mul_of_nonneg_left happrox hM

theorem exists_translated_shift_testing_bound (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p rho R error M : ℝ},
      0 ≤ p → 0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      (p + C) ^ C ≤ R → 0 ≤ error → 0 ≤ M →
      ∀ (v J : ZMod N → ℝ) (E : Finset (ZMod N)),
      CyclicNiltestShiftBound.{0} s N R error v J E →
      ∀ h ∉ E, (∀ x, |v x * J (x + h)| ≤ M) →
      ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} s N p f → ∀ b : ZMod N,
      (𝔼 x, v x * J (x + h) * f (b + x)) ≤
        Real.exp ((p + C) ^ C) * error + M * (6 * rho + 3 / N) := by
  obtain ⟨C, hC, htranslation⟩ := exists_positive_cyclic_translation_approximation a
  refine ⟨C, hC, ?_⟩
  intro s N _ p rho R error M hp hrho hrhoinv hR herror hM v J E hbound h hh hw f hf b
  obtain ⟨n, _, hn, U, hU, _, _, hmean⟩ := htranslation hp hrho hrhoinv f hf b
  have hpiece (i) : (𝔼 x, (v x * J (x + h)) * U i x) ≤ error :=
    ((hU i).mono le_rfl hR).apply_shiftBound hbound hh
  apply (expect_weighted_sum_approximation_le (fun x => v x * J (x + h))
    (fun x => f (b + x)) U hM hw hmean hpiece).trans
  simpa only [Fintype.card_fin] using add_le_add
    (mul_le_mul_of_nonneg_right hn herror) (le_refl (M * (6 * rho + 3 / N)))

end Erdos3

end

end OAI
