/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteCellMean {X A : Type*} [Fintype X] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (f : X → ℝ) (a : A) : ℝ :=
  p.mean (fun x => if C x = a then f x else 0)

theorem finiteCellMean_sum {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (f : X → ℝ) :
    (∑ a, finiteCellMean p C f a) = p.mean f := by
  unfold finiteCellMean
  rw [← p.mean_sum]
  congr 1
  funext x
  simp

noncomputable def finiteCellWeights {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) : FiniteProbabilityWeights A where
  weight a := finiteCellMean p C (fun _ => 1) a
  nonneg a := p.mean_nonneg (fun x => by split_ifs <;> norm_num)
  total := by rw [finiteCellMean_sum, p.mean_const]

noncomputable def finiteCellResidueMean {X A R : Type*}
    [Fintype X] [DecidableEq A] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) : ℝ :=
  p.mean (fun x => if C x = a ∧ F x = r then e x else 0)

theorem finite_cell_energy_aggregate {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (e : X → ℝ) {E : ℝ}
    (he : ∀ a, finiteCellMean p C (fun x => e x ^ 2) a ≤ E * (finiteCellWeights p C).weight a) :
    p.mean (fun x => e x ^ 2) ≤ E := by
  rw [← finiteCellMean_sum p C]
  calc
    _ ≤ ∑ a, E * (finiteCellWeights p C).weight a := Finset.sum_le_sum (fun a _ => he a)
    _ = E := by rw [← Finset.mul_sum, (finiteCellWeights p C).total, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniform_subtype_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniform Ω).mean (fun z => if P z then f z else 0) =
      (Fintype.card {z // P z} : ℝ) / Fintype.card Ω * (𝔼 z : {z // P z}, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ z, if P z then f z else 0) = ∑ z : {z // P z}, f z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_mul_expect (fun z : {z // P z} => f z.val)]
  ring

theorem uniform_observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ (FiniteProbabilityWeights.uniform Ω) F f) x =
      ((Fintype.card {z // ∀ i ∈ S, F z i = x i} : ℝ) / Fintype.card Ω /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) *
      (𝔼 z : {z // ∀ i ∈ S, F z i = x i}, f z.val) := by
  classical
  rw [observedProductDensity_conditional μ hμ]
  have hf : (fun z => f z * productFiberIndicator S x (F z)) =
      (fun z => if ∀ i ∈ S, F z i = x i then f z else 0) := by
    funext z
    unfold productFiberIndicator
    split_ifs <;> simp
  rw [hf, uniform_subtype_mean]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteCellMean_uniform {X A : Type*} [Fintype X] [Nonempty X] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X *
        (𝔼 x : {x // C x = a}, f x.val) :=
  uniform_subtype_mean (fun x => C x = a) f

theorem finiteCellWeights_uniform {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (a : A) :
    (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X := by
  change finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun _ => 1) a = _
  rw [finiteCellMean_uniform]
  by_cases h : Nonempty {x // C x = a}
  · let : Nonempty {x // C x = a} := h
    simp
  · let : IsEmpty {x // C x = a} := not_nonempty_iff.mp h
    simp

theorem finiteCellMean_uniform_weighted {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, f x.val) := by
  rw [finiteCellWeights_uniform, finiteCellMean_uniform]

theorem finiteCellResidueMean_uniform {X A R : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A] [DecidableEq R]
    (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) :
    finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, if F x.val = r then e x.val else 0) := by
  have h : finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r =
      finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun x => if F x = r then e x else 0) a := by
    unfold finiteCellResidueMean finiteCellMean
    apply congrArg (FiniteProbabilityWeights.uniform X).mean
    funext x
    by_cases hc : C x = a <;> by_cases hf : F x = r <;> simp [hc, hf]
  rw [h, finiteCellMean_uniform_weighted]

theorem uniform_cell_residue_bound {X A R : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A] [DecidableEq R]
    (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) {delta : ℝ}
    (he : |𝔼 x : {x // C x = a}, if F x.val = r then e x.val else 0| ≤ delta) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a * delta := by
  rw [finiteCellResidueMean_uniform, abs_mul,
    abs_of_nonneg ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg a)]
  exact mul_le_mul_of_nonneg_left he ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg a)

theorem uniform_cell_energy_aggregate {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (e : X → ℝ) {E : ℝ}
    (he : ∀ a, (𝔼 x : {x // C x = a}, e x.val ^ 2) ≤ E) :
    (FiniteProbabilityWeights.uniform X).mean (fun x => e x ^ 2) ≤ E := by
  apply finite_cell_energy_aggregate (FiniteProbabilityWeights.uniform X) C e
  intro a
  rw [finiteCellMean_uniform_weighted]
  exact (mul_le_mul_of_nonneg_left (he a)
    ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg a)).trans_eq (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {X T A B : Type*} [Fintype X] [Fintype T] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] in
theorem finiteCellMean_product (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights T)
    (C : X → A) (E : T → B) (f : X → T → ℝ) (a : A) (b : B) :
    finiteCellMean (q.prod p) (fun tx => (C tx.2, E tx.1)) (fun tx => f tx.2 tx.1) (a,b) =
      finiteCellMean p C (fun x => finiteCellMean q E (f x) b) a := by
  unfold finiteCellMean
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm]
  congr 1
  funext x
  by_cases hx : C x = a
  · simp only [hx, Prod.mk.injEq, true_and, ite_true]
  · have he (t : T) : (if (C x, E t) = (a,b) then f x t else 0) = 0 := by
      simp [hx]
    simp only [he, q.mean_const, ite_eq_right hx]

theorem finiteCellWeights_product (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights T)
    (C : X → A) (E : T → B) (a : A) (b : B) :
    (finiteCellWeights (q.prod p) (fun tx => (C tx.2, E tx.1))).weight (a,b) =
      (finiteCellWeights p C).weight a * (finiteCellWeights q E).weight b := by
  change finiteCellMean (q.prod p) _ (fun _ => 1) (a,b) = _
  rw [finiteCellMean_product p q C E (fun _ _ => 1)]
  change p.mean (fun x => if C x = a then (finiteCellWeights q E).weight b else 0) = _
  have he : (fun x => if C x = a then (finiteCellWeights q E).weight b else 0) =
      (fun x => (if C x = a then 1 else 0) * (finiteCellWeights q E).weight b) := by
    funext x
    split_ifs <;> simp
  rw [he, p.mean_mul_const]
  rfl

theorem finiteCellMean_product_uniform [Nonempty X] [Nonempty T]
    (C : X → A) (E : T → B) (f : X → T → ℝ) (a : A) (b : B) :
    finiteCellMean ((FiniteProbabilityWeights.uniform T).prod (FiniteProbabilityWeights.uniform X))
      (fun tx => (C tx.2, E tx.1)) (fun tx => f tx.2 tx.1) (a,b) =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (finiteCellWeights (FiniteProbabilityWeights.uniform T) E).weight b *
        (𝔼 x : {x // C x = a}, 𝔼 t : {t // E t = b}, f x.val t.val) := by
  rw [finiteCellMean_product]
  simp only [finiteCellMean_uniform_weighted]
  rw [← Finset.mul_expect]
  ring

end Erdos3

end

end OAI
