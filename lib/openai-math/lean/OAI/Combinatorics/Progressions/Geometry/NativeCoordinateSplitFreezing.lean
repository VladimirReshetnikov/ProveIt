import Mathlib.Order.UpperLower.Basic
import OAI.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem eval_eq_of_support_agreement {σ R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (p : VectorPolynomial σ R V) (x y : σ → R)
    (hxy : ∀ a, coefficients p a ≠ 0 → ∀ i, a i ≠ 0 → x i = y i) :
    eval x p = eval y p := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hxy a (Finsupp.mem_support_iff.mp ha) i (Finsupp.mem_support_iff.mp hi)]

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

theorem polynomialOrbitEval_eq_on_active_coordinates {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
    (F : MultidegreeLieFiltration σ L s bound) (g : F.PolynomialOrbit)
    (x y : σ → ℤ) (hxy : ∀ i, bound i ≠ 0 → x i = y i) :
    F.polynomialOrbitEval x g = F.polynomialOrbitEval y g := by
  apply NilpotentLieBCHGroup.ext
  apply VectorPolynomial.eval_eq_of_support_agreement (g.log F)
  intro a ha i hi
  have hle : (fun j => a j) ≤ bound := by
    by_contra hn
    have hc := g.adapted F a
    exact ha (by simpa only [F.terminal _ hn, Submodule.mem_bot] using hc)
  have hb : bound i ≠ 0 := by
    intro hz
    exact hi (Nat.eq_zero_of_le_zero (by simpa only [hz] using hle i))
  exact congrArg (fun z : ℤ => (z : ℚ)) (hxy i hb)

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def coordinateSplitBound (s : ℕ) (i : σ) (b : Bool) (j : σ) : ℕ :=
  if b then (if j = i then s - 1 else s) else (if j = i then s else 0)

def coordinateSplitDownset (s : ℕ) (i : σ) (b : Bool) : Set (σ →₀ ℕ) :=
  {a | ∀ j, a j ≤ coordinateSplitBound s i b j}

theorem coordinateSplitBound_le (s : ℕ) (i : σ) (b : Bool) :
    coordinateSplitBound s i b ≤ fun _ => s := by
  intro j
  cases b <;> by_cases h : j = i <;> simp [coordinateSplitBound, h]

theorem coordinateSplitDownset_lower (s : ℕ) (i : σ) (b : Bool) :
    IsLowerSet (coordinateSplitDownset s i b) :=
  fun _ _ hab hb j => (hab j).trans (hb j)

theorem coordinateSplitDownset_covers [Fintype σ] (s : ℕ) (i : σ) (a : σ →₀ ℕ)
    (ha : (∑ j, a j) ≤ s) :
    a ∈ coordinateSplitDownset s i false ∪ coordinateSplitDownset s i true := by
  have hall (j : σ) : a j ≤ s :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)).trans ha
  by_cases hi : a i ≤ s - 1
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simpa [coordinateSplitBound] using hi
    · simpa [coordinateSplitBound, hj] using hall j
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simpa [coordinateSplitBound] using hall i
    · have htwo : a i + a j ≤ ∑ k, a k := by
        calc
          a i + a j = ∑ k ∈ ({i, j} : Finset σ), a k := by simp [Ne.symm hj]
          _ ≤ ∑ k, a k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hz : a j = 0 := by omega
      simp [coordinateSplitBound, hj, hz]

theorem coordinateSplitDownset_terminal [Fintype σ] [Nonempty σ]
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (i : σ) (a : σ →₀ ℕ)
    (ha : a ∉ coordinateSplitDownset s i false ∪ coordinateSplitDownset s i true) :
    (F.totalDegreeMultifiltration σ).layer (fun j => a j) = ⊥ := by
  apply F.layer_eq_bot_above_step
  exact Nat.lt_of_not_ge (fun h => ha (coordinateSplitDownset_covers s i a h))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCoordinateSplit {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (i : σ) (s d : ℕ) (p epsilon : ℝ) (f : (σ → ℤ) → ℂ) where
  count : ℕ
  count_pos : 0 < count
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Bool → Type
  [lie : ∀ b, LieRing (L b)]
  [algebra : ∀ b, LieAlgebra ℚ (L b)]
  dim : Bool → ℕ
  [topology : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] L b)]
  [topologicalAdd : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] L b)]
  [continuousSMul : ∀ b, ContinuousSMul ℝ (ℝ ⊗[ℚ] L b)]
  [hausdorff : ∀ b, T2Space (ℝ ⊗[ℚ] L b)]
  model : ∀ b, RationalFilteredNilmanifold (L b) (∑ _ : σ, s) (dim b)
  multi : ∀ b, (model b).MultidegreeStructure (coordinateSplitBound s i b)
  complexity : ∀ b, (multi b).ComplexityLE p
  dimension_bound : ∀ b, dim b ≤ 2 ^ (Fintype.card σ * s) * d
  orbit : ∀ b, (multi b).filtration.realification.PolynomialOrbit
  test : ∀ b, Fin count → (model b).Niltest (fun _ : σ => 1)
  test_norm : ∀ b j, (test b j).normBound ≤ 1
  test_complexity : ∀ b j, (test b j).ComplexityLE p
  test_orbit : ∀ b j, (test b j).orbit = (multi b).orbitToOrdinary (orbit b)
  approximation : ∀ x, ‖f x - ∑ j, (test false j).eval x * (test true j).eval x‖ ≤ epsilon

end Erdos3

end

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_fixed_correlating_term {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {i : σ} {G X : Type*} {s d : ℕ} {p epsilon rho : ℝ} {u : (σ → ℤ) → ℂ}
    (R : NativeCoordinateSplit i s d p epsilon u) (H : Finset G) (hH : H.Nonempty)
    (S : G → Finset X) (hS : ∀ h ∈ H, (S h).Nonempty)
    (sample : G → X → σ → ℤ) (f : G → X → ℂ)
    (hrho : 0 < rho) (hepsilon : epsilon ≤ rho / 2)
    (hf : ∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, rho ≤ ‖𝔼 x ∈ S h, f h x * star (u (sample h x))‖) :
    ∃ (j : Fin R.count) (Q : Finset G), Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-p) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ h ∈ Q, rho / (2 * Real.exp p) ≤
        ‖𝔼 x ∈ S h, f h x * star ((R.test false j).eval (sample h x) *
          (R.test true j).eval (sample h x))‖ := by
  classical
  let rel (h : G) (_ : Unit) (j : Fin R.count) : Prop :=
    rho / (2 * Real.exp p) ≤
      ‖𝔼 x ∈ S h, f h x * star ((R.test false j).eval (sample h x) *
        (R.test true j).eval (sample h x))‖
  have hcount : (Fintype.card (Fin R.count) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using R.count_bound
  have hchoice : ∀ h ∈ H, ∀ b, ∃ j, rel h b j := by
    intro h hh _
    apply exists_correlating_summand (J := Fin R.count) (hS h hh)
      (f h) (fun x => u (sample h x))
      (fun j x => (R.test false j).eval (sample h x) * (R.test true j).eval (sample h x))
      hrho (Real.exp_pos p) hcount (hf h hh) _ (hcorr h hh)
    intro x _
    rw [norm_sub_rev]
    exact (R.approximation (sample h x)).trans hepsilon
  obtain ⟨j, Q, hsub, hQ, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  refine ⟨j (), Q, hsub, hQ, ?_, fun h hh => hfixed h hh ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeCoordinateSplit

end

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ] {i : σ} {s d : ℕ}
  {p epsilon : ℝ} {f : (σ → ℤ) → ℂ} (R : NativeCoordinateSplit i s d p epsilon f)

theorem first_eval_eq (j : Fin R.count) (x y : σ → ℤ) (hxy : x i = y i) :
    (R.test false j).eval x = (R.test false j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit false j, (R.multi false).orbitToOrdinary_eval,
    (R.multi false).orbitToOrdinary_eval]
  apply congrArg (R.test false j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi false).filtration.realification.polynomialOrbitEval_eq_on_active_coordinates
  intro k hk
  have hki : k = i := by
    by_contra hn
    exact hk (by simp [coordinateSplitBound, hn])
  subst k
  exact hxy

noncomputable def firstFactor (j : Fin R.count) (n : ℤ) : ℂ :=
  (R.test false j).eval (fun _ => n)

theorem first_eval_firstFactor (j : Fin R.count) (x : σ → ℤ) :
    (R.test false j).eval x = R.firstFactor j (x i) :=
  R.first_eval_eq j x (fun _ => x i) rfl

theorem firstFactor_norm (j : Fin R.count) (n : ℤ) : ‖R.firstFactor j n‖ ≤ 1 :=
  ((R.test false j).norm_eval_le _).trans
    (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)

end Erdos3.NativeCoordinateSplit

end

section

namespace Erdos3.NativeCoordinateSplit

open Module RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_second_expansion_budget (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {i : σ} {d : ℕ} {p epsilon : ℝ} {f : (σ → ℤ) → ℂ}
      (R : NativeCoordinateSplit i s d p epsilon f) (j : Fin R.count) (b : σ → ℤ),
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => (R.test true j).eval (Function.update b i (x ()))), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_controlled_frozen_niltest (∑ _ : σ, s)
  refine ⟨C, hC, ?_⟩
  intro i d p epsilon f R j b
  classical
  let S : Finset σ := {i}
  have hp : 0 ≤ p := (Nat.cast_nonneg (R.dim true)).trans (R.complexity true).1.1
  have hlip : ((R.test true j).lipBound : ℝ) ≤ Real.exp p := by
    have hb := (R.test true j).observable_budget (R.test_complexity true j)
    have hn := (R.test true j).normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖(R.test true j).observable x‖ ≤ (1 : ℝ) := fun x =>
    ((R.test true j).norm_le x).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  obtain ⟨E, _, _, hE⟩ := hfreeze (R.model true) (R.multi true) S b
    (R.orbit true) (R.test true j).observable (R.test true j).lipBound 1
    (R.test true j).lipschitz hub (R.complexity true) hlip
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  let K := (R.multi true).filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨T, _, hT, _, hTeval⟩ := hE
  let U := T.affinePullback (fun _ (_ : Unit) => (1 : ℤ)) 0
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = (R.test true j).eval (Function.update b i (x ())) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, hTeval]
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval]
    congr 2
    apply congrArg (fun z => (R.multi true).filtration.realification.polynomialOrbitEval z
      (R.orbit true))
    funext k
    by_cases hk : k = i
    · subst k
      simp [S, freezeCoordinates, integerAffineMap]
    · simp [S, freezeCoordinates, hk]
  have hdegree : multidegreeWeight (retainedCoordinateWeight S) (coordinateSplitBound s i true) =
      s - 1 := by
    rw [retainedCoordinate_degree]
    simp [S, coordinateSplitBound]
  have hresult : ∃ Q : NativeIntegerExpansion (fun _ : Unit => 1)
      (multidegreeWeight (retainedCoordinateWeight S) (coordinateSplitBound s i true))
      ((p + C) ^ C) (fun x => (R.test true j).eval (Function.update b i (x ()))), Q.count = 1 :=
    ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩
  exact hdegree ▸ hresult

end Erdos3.NativeCoordinateSplit

end

end OAI
