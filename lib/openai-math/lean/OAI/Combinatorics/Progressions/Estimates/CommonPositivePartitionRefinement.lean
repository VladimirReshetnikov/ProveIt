/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition

namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

structure PositiveCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = (test.evalCyclic N (fun _ => x)).re

theorem PositiveCyclicNiltest.model_nonempty {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) (hp : 0 ≤ p) :
    Nonempty (PositiveCyclicModel.{u} degree N (raisedNiltestBudget p) f) := by
  rcases hf with @⟨L, lie, algebra, s, dim, topology, topologicalAdd, continuousSMul,
    hausdorff, D, hdegree, T, hpositive, hcomplexity, heval⟩
  refine ⟨{
    L := L
    lie := lie
    algebra := algebra
    dim := dim
    topology := topology
    topologicalAdd := topologicalAdd
    continuousSMul := continuousSMul
    hausdorff := hausdorff
    model := D.raiseStep hdegree
    test := T.raiseStep hdegree
    positive := T.raiseStep_unit_interval hdegree hpositive
    complexity := T.raiseStep_complexity hdegree hp hcomplexity
    eval := ?_ }⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
  exact heval x

end Erdos3

end

section

universe u

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct

theorem prod {ι : Type} [Fintype ι] {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ι → ZMod N → ℝ} (hf : ∀ i, PositiveCyclicNiltest.{u} degree N p (f i))
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) :
    PositiveCyclicNiltest.{u} degree N (productNiltestBudget (raisedNiltestBudget p))
      (fun x => ∏ i, f i x) := by
  classical
  let R := fun i => Classical.choice ((hf i).model_nonempty hp)
  let L := fun i => (R i).L
  let : ∀ i, LieRing (L i) := fun i => (R i).lie
  let : ∀ i, LieAlgebra ℚ (L i) := fun i => (R i).algebra
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i) := fun i => (R i).topology
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i) := fun i => (R i).topologicalAdd
  let : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i) := fun i => (R i).continuousSMul
  let : ∀ i, T2Space (ℝ ⊗[ℚ] L i) := fun i => (R i).hausdorff
  let D := fun i => (R i).model
  let T := fun i => (R i).test
  let : FiniteDimensional ℚ (∀ i, L i) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hι' : (Fintype.card ι : ℝ) ≤ raisedNiltestBudget p := hι.trans (le_raisedNiltestBudget p)
  let S := RationalFilteredNilmanifold.piNiltest D T hp' hι' (fun i => (R i).complexity)
  refine .of_test (RationalFilteredNilmanifold.pi D) le_rfl S
    (RationalFilteredNilmanifold.piNiltest_unit_interval D T hp' hι'
      (fun i => (R i).complexity) (fun i => (R i).positive))
    (RationalFilteredNilmanifold.piNiltest_complexity D T hp' hι' (fun i => (R i).complexity)) ?_
  intro x
  have he (i : ι) : (T i).eval (fun _ : Unit => (x.val : ℤ)) = (f i x : ℂ) := by
    apply Complex.ext
    · change ((R i).test.evalCyclic N (fun _ : Unit => x)).re = f i x
      exact ((R i).eval x).symm
    · simpa only [Complex.ofReal_im] using ((T i).unit_interval_eval (R i).positive _).1
  change (∏ i, f i x) = ((RationalFilteredNilmanifold.piNiltest D T hp' hι'
    (fun i => (R i).complexity)).eval (fun _ : Unit => (x.val : ℤ))).re
  rw [RationalFilteredNilmanifold.piNiltest_eval]
  simp_rw [he]
  rw [← Complex.ofReal_prod]
  rfl

end Erdos3.PositiveCyclicNiltest

end

section

universe u

namespace Erdos3

open scoped BigOperators

theorem real_shift_weighted_mean {N : ℕ} [NeZero N] (a J : ZMod N → ℝ)
    (T : ZMod N → ℂ) (h : ZMod N) :
    (𝔼 n, ((a n * J (n + h) : ℝ) : ℂ) * T n).re =
      𝔼 n, a n * J (n + h) * (T n).re := by
  simp only [expect_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem shift_violation_weight_cap {N : ℕ} {p epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (f g J : ZMod N → ℝ)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p)
    (hJ : ∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) (h n : ZMod N) :
    ‖((((f n - (1 + epsilon) * g n) * J (n + h)) : ℝ) : ℂ)‖ ≤
      Real.exp (2 * p + 2) := by
  have ha : |f n - (1 + epsilon) * g n| ≤ 2 * Real.exp p := by
    apply abs_le.mpr
    have hprod : (1 + epsilon) * g n ≤ 2 * Real.exp p :=
      (mul_le_mul_of_nonneg_right (by linarith : 1 + epsilon ≤ 2) (hg n).1).trans
        (mul_le_mul_of_nonneg_left (hg n).2 (by norm_num))
    have hprod0 : 0 ≤ (1 + epsilon) * g n := mul_nonneg (by linarith) (hg n).1
    constructor <;> linarith [(hf n).1, (hf n).2, Real.exp_pos p]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJ _).1]
  calc
    _ ≤ (2 * Real.exp p) * Real.exp p := mul_le_mul ha (hJ _).2 (hJ _).1 (by positivity)
    _ ≤ (Real.exp 2 * Real.exp p) * Real.exp p := by gcongr
    _ = Real.exp (2 * p + 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem exists_many_positive_cyclic_violations {degree N : ℕ} [NeZero N]
    (a J : ZMod N → ℝ) {p error sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hfailure : ¬ ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ sigma * N ∧
      CyclicNiltestShiftBound.{u} degree N p error a J E) :
    ∃ (H : Finset (ZMod N)) (T : ZMod N → ZMod N → ℝ),
      H.Nonempty ∧ sigma * N < (H.card : ℝ) ∧
      (∀ h, PositiveCyclicNiltest.{u} degree N p (T h)) ∧
      ∀ h ∈ H, error < 𝔼 n, a n * J (n + h) * T h n := by
  classical
  let H : Finset (ZMod N) := Finset.univ.filter fun h =>
    ∃ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N p T ∧
      error < 𝔼 n, a n * J (n + h) * T n
  have hbound : CyclicNiltestShiftBound.{u} degree N p error a J H := by
    intro h hh L _ _ s d _ _ _ _ D hs T hT hTc
    by_contra hbad
    apply hh
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun n => (T.evalCyclic N (fun _ => n)).re,
      PositiveCyclicNiltest.of_test D hs T hT hTc (fun _ => rfl), lt_of_not_ge hbad⟩
  have hlarge : sigma * N < (H.card : ℝ) :=
    lt_of_not_ge (fun hsmall => hfailure ⟨H, hsmall, hbound⟩)
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_le_of_lt (mul_nonneg hsigma (Nat.cast_nonneg N)) hlarge)
  obtain ⟨h₀, hh₀⟩ := hH
  let pick (h : ZMod N) := if h ∈ H then h else h₀
  have hpick (h : ZMod N) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hh₀
  have hchoices (h : ZMod N) : ∃ T : ZMod N → ℝ,
      PositiveCyclicNiltest.{u} degree N p T ∧
      error < 𝔼 n, a n * J (n + pick h) * T n := by
    simpa only [H, Finset.mem_filter, Finset.mem_univ, true_and] using hpick h
  choose T hT hcorr using hchoices
  refine ⟨H, T, ⟨h₀, hh₀⟩, hlarge, hT, ?_⟩
  intro h hh
  simpa only [pick, ite_eq_left hh] using hcorr h

end Erdos3

end

section

namespace Erdos3

theorem exists_common_positive_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {I : ι → Type} [∀ i, Fintype (I i)] {degree N : ℕ} [NeZero N]
      (A : ∀ i, I i → ZMod N → ℝ) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (Fintype.card (I i) : ℝ) ≤ Real.exp p) →
      (∀ i j, PositiveCyclicNiltest.{0} degree N p (A i j)) →
      (∀ i x, ∑ j, A i j x = 1) →
      ∃ U : (∀ i, I i) → ZMod N → ℝ,
        (Fintype.card (∀ i, I i) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j)) ∧
        (∀ x, ∑ j, U j x = 1) ∧
        (∀ j x, 0 < U j x → ∀ i, 0 < A i (j i) x) ∧
        ∀ (h : ZMod N) j k x, 0 < U j x * U k (x + h) →
          ∀ i, 0 < A i (j i) x * A i (k i) (x + h) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 2 + 3
  let P := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X ^ 2 + P)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ I _ degree N _ A p hp hι hcard hA hsum
  classical
  have hcost : p ^ 2 + productNiltestBudget (raisedNiltestBudget p) ≤ (p + C) ^ C := by
    simpa [X, R, P, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hP : 0 ≤ productNiltestBudget (raisedNiltestBudget p) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget p) ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (sq_nonneg p)).trans hcost
  have hsquare : p ^ 2 ≤ (p + C) ^ C := (le_add_of_nonneg_right hP).trans hcost
  let U : (∀ i, I i) → ZMod N → ℝ := fun j x => ∏ i, A i (j i) x
  have hU (j : ∀ i, I i) : PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j) :=
    ((PositiveCyclicNiltest.prod (fun i => hA i (j i)) hp hι)).mono le_rfl hproduct
  have hsupport (j : ∀ i, I i) (x : ZMod N) (hx : 0 < U j x) (i : ι) :
      0 < A i (j i) x := by
    have hne : A i (j i) x ≠ 0 := by
      intro hz
      have hzero : U j x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      linarith
    exact lt_of_le_of_ne ((hA i (j i)).unit_interval x).1 (Ne.symm hne)
  refine ⟨U, ?_, hU, ?_, hsupport, ?_⟩
  · rw [Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _i : ι, Real.exp p :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcard i)
      _ = Real.exp (Fintype.card ι * p) := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
      _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := Real.exp_le_exp.mpr hsquare
  · intro x
    change (∑ j : ∀ i, I i, ∏ i, A i (j i) x) = 1
    rw [← Fintype.prod_sum (fun i (j : I i) => A i j x)]
    simp only [hsum, Finset.prod_const_one]
  · intro h j k x hx i
    have hpos : 0 < U j x ∧ 0 < U k (x + h) := by
      rcases mul_pos_iff.mp hx with h | h
      · exact h
      · linarith [((hU j).unit_interval x).1]
    exact mul_pos (hsupport j x hpos.1 i) (hsupport k (x + h) hpos.2 i)

end Erdos3

end

section

namespace Erdos3

theorem exists_common_positive_partition_refinement (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {I : ι → Type} [∀ i, Fintype (I i)] {degree q N : ℕ} [NeZero q] [NeZero N]
      (A : ∀ i, I i → ZMod N → ℝ) {p ρ : ℝ},
      1 ≤ degree → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (Fintype.card (I i) : ℝ) ≤ Real.exp p) →
      (∀ i j, PositiveCyclicNiltest.{0} degree N p (A i j)) →
      (∀ i x, ∑ j, A i j x = 1) → (q : ℝ) ≤ Real.exp p →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧
        (Fintype.card (((∀ i, I i) × ZMod q) × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (((∀ i, I i) × ZMod q) × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < U j x → 0 < U j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (∀ j x, 0 < U j x → ∀ i, 0 < A i (j.1.1 i) x) ∧
          ∀ (h : ZMod N) j k x, 0 < U j x * U k (x + h) →
            ∀ i, 0 < A i (j.1.1 i) x * A i (k.1.1 i) (x + h) := by
  obtain ⟨B, _, hcommon⟩ := exists_common_positive_partition
  obtain ⟨R, _, hresidue⟩ := exists_controlled_residue_refinement
  obtain ⟨S, _, hinterval⟩ := exists_interval_refined_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let V := T + (T + Polynomial.C R) ^ R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (V + Polynomial.C S) ^ S)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ I _ degree q N _ _ A p ρ hdegree hp hι hcard hA hsum hq hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  let r := t + (t + R) ^ R
  have htr : t ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := ht.trans htr
  have hRr : (t + R) ^ R ≤ r := le_add_of_nonneg_left ht
  have htotal : r + (r + S) ^ S ≤ (p + C) ^ C := by
    simpa [X, T, V, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hSC : (r + S) ^ S ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans htotal
  obtain ⟨U₀, hcount₀, hU₀, hsum₀, hsupport₀, _⟩ := hcommon A hp hι hcard hA hsum
  obtain ⟨U₁, hcount₁, hU₁, hsum₁, hsupport₁⟩ :=
    hresidue U₀ ht hdegree (hcount₀.trans (Real.exp_le_exp.mpr hBt))
      (hq.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hU₀ j).mono le_rfl hBt) hsum₀
  obtain ⟨n, hn, hcount, U, hU, hUsum, hsupport₂, hcircle, hbad, _⟩ :=
    hinterval U₁ hdegree hr (hcount₁.trans (Real.exp_le_exp.mpr hRr))
      (fun j => (hU₁ j).mono le_rfl hRr) hsum₁ hρ
      (hρinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ r + 2) a)))
  have hsupport j x (hx : 0 < U j x) : ∀ i, 0 < A i (j.1.1 i) x :=
    hsupport₀ j.1.1 x (hsupport₁ j.1 x (hsupport₂ j x hx)).1
  refine ⟨n, hn, hcount.trans (Real.exp_le_exp.mpr hSC), U,
    fun j => (hU j).mono le_rfl hSC, hUsum,
    fun j x hx => (hsupport₁ j.1 x (hsupport₂ j x hx)).2,
    hcircle, hbad, hsupport, ?_⟩
  intro h j k x hx i
  have hpos : 0 < U j x ∧ 0 < U k (x + h) := by
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hU j).unit_interval x).1]
  exact mul_pos (hsupport j x hpos.1 i) (hsupport k (x + h) hpos.2 i)

end Erdos3

end

end OAI
