/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteOrderedSubsetSum
import OAI.Combinatorics.Progressions.Estimates.FiniteSectionVanishing
import OAI.Combinatorics.Progressions.Estimates.ProductMeanPullback
import OAI.Combinatorics.Progressions.Geometry.FiniteGoodSupport
import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)]

def ProductNoSingletonCoordinate (S : J → Finset I) {q : ℕ} (a : Fin q → J) : Prop :=
  ∀ i, (Finset.univ.filter (fun r => i ∈ S (a r))).card ≠ 1

noncomputable def productANOVAMomentChoices (S : J → Finset I) (q : ℕ) : Finset (Fin q → J) := by
  classical
  exact Finset.univ.filter (ProductNoSingletonCoordinate S)

theorem productANOVA_moment_expansion (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ) (q : ℕ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ j, productANOVA μ (S j) (f j) x) ^ q) =
      ∑ a : Fin q → J, (FiniteProbabilityWeights.pi μ).mean
        (fun x => ∏ r, productANOVA μ (S (a r)) (f (a r)) x) := by
  simp_rw [Fintype.sum_pow]
  exact FiniteProbabilityWeights.mean_sum _ _ _

omit [Fintype J] in
theorem productANOVA_term_zero_of_singleton_count (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ) {q : ℕ} (a : Fin q → J)
    (i : I) (hi : (Finset.univ.filter (fun r => i ∈ S (a r))).card = 1) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ r, productANOVA μ (S (a r)) (f (a r)) x) = 0 := by
  classical
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hi
  have hi₀ : i ∈ S (a r₀) := by
    have hr : r₀ ∈ Finset.univ.filter (fun r => i ∈ S (a r)) := by
      rw [hr₀]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hr).2
  apply productANOVA_unique_coordinate_zero μ Finset.univ (fun r => S (a r))
    (fun r => f (a r)) (Finset.mem_univ r₀) hi₀
  intro r _ hne hir
  have hr : r ∈ Finset.univ.filter (fun r => i ∈ S (a r)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hir⟩
  rw [hr₀] at hr
  exact hne (Finset.mem_singleton.mp hr)

theorem productANOVA_moment_without_singletons (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ) (q : ℕ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ j, productANOVA μ (S j) (f j) x) ^ q) =
      ∑ a ∈ productANOVAMomentChoices S q, (FiniteProbabilityWeights.pi μ).mean
        (fun x => ∏ r, productANOVA μ (S (a r)) (f (a r)) x) := by
  classical
  rw [productANOVA_moment_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset (ProductNoSingletonCoordinate S) Finset.univ)
  intro a _ ha
  have hbad : ¬ ProductNoSingletonCoordinate S a := by
    simpa only [productANOVAMomentChoices, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  unfold ProductNoSingletonCoordinate at hbad
  push Not at hbad
  obtain ⟨i, hi⟩ := hbad
  exact productANOVA_term_zero_of_singleton_count μ S f a i hi

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def coordinateUnionWeight (z : Sigma X) : ℝ := (μ z.1).weight z.2

omit [Fintype I] [LinearOrder I] in
theorem coordinateUnionWeight_nonneg (z : Sigma X) : 0 ≤ coordinateUnionWeight μ z :=
  (μ z.1).nonneg z.2

noncomputable def productANOVATensor (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) : ℝ := by
  classical
  exact if h : StrictMono (fun j => (z j).1) then
    if (∏ j, coordinateUnionWeight μ (z j)) = 0 then 0 else
      productANOVA μ (Finset.univ.image (fun j => (z j).1)) f
        (productTuplePoint (fun j => (z j).1) h.injective (fun j => (z j).2) base)
    else 0

theorem productANOVATensor_zero_of_not_ordered (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X)
    (hz : ¬StrictMono (fun j => (z j).1)) : productANOVATensor μ k base f z = 0 := by
  simp only [productANOVATensor, hz, dite_false]

theorem productANOVATensor_zero_of_zero_weight (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) (j : Fin k)
    (hj : coordinateUnionWeight μ (z j) = 0) : productANOVATensor μ k base f z = 0 := by
  have hw : (∏ i, coordinateUnionWeight μ (z i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hj
  simp [productANOVATensor, hw]

theorem productANOVATensor_zero_of_repeated (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) (j l : Fin k)
    (hjl : j ≠ l) (he : (z j).1 = (z l).1) : productANOVATensor μ k base f z = 0 := by
  apply productANOVATensor_zero_of_not_ordered μ k base f z
  intro h
  exact hjl (h.injective he)

theorem productANOVATensor_basepoint (k : ℕ) (base base' : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) :
    productANOVATensor μ k base f z = productANOVATensor μ k base' f z := by
  classical
  by_cases hz : StrictMono (fun j => (z j).1)
  · simp only [productANOVATensor, hz, dite_true]
    split_ifs with hw
    · rfl
    · apply productANOVA_depends μ (Finset.univ.image (fun j => (z j).1)) f
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact (productTuplePoint_apply _ hz.injective (fun j => (z j).2) base j).trans
        (productTuplePoint_apply _ hz.injective (fun j => (z j).2) base' j).symm
  · simp only [productANOVATensor, hz, dite_false]

theorem productANOVATensor_weighted_sq (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : Fin k → I) (v : ∀ j, X (a j)) :
    (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v *
      productANOVATensor μ k base f (fun j => ⟨a j, v j⟩) ^ 2 =
    if ha : StrictMono a then
      (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v *
        productANOVA μ (Finset.univ.image a) f (productTuplePoint a ha.injective v base) ^ 2
    else 0 := by
  classical
  by_cases ha : StrictMono a
  · simp only [productANOVATensor, ha, dite_true]
    change _ * (if (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v = 0 then 0 else _) ^ 2 = _
    by_cases hw : (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v = 0
    · simp only [hw, zero_mul]
    · simp only [hw, ite_false]
  · simp only [productANOVATensor, ha, dite_false, zero_pow (by decide : 2 ≠ 0), mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_evaluate (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : Fin k → I) (x : ∀ i, X i)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    productANOVATensor μ k base f (fun j => ⟨a j, x (a j)⟩) =
      if StrictMono a then productANOVA μ (Finset.univ.image a) f x else 0 := by
  classical
  have hw : (∏ j, coordinateUnionWeight μ (⟨a j, x (a j)⟩ : Sigma X)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Finset.prod_ne_zero_iff.mp hx (a j) (Finset.mem_univ _)
  by_cases ha : StrictMono a
  · simp only [productANOVATensor, ha, dite_true, hw, ite_false, ite_true]
    exact (productANOVA_depends μ (Finset.univ.image a) f).tuplePoint ha.injective x base
  · simp only [productANOVATensor, ha, dite_false, ite_false]

theorem productANOVATensor_sum_evaluate (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    (∑ a : Fin k → I, productANOVATensor μ k base f (fun j => ⟨a j, x (a j)⟩)) =
      ∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x := by
  simp_rw [productANOVATensor_evaluate μ k base f _ x hx]
  exact finiteOrderedSubset_sum k (fun S => productANOVA μ S f x)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_null_section (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (s : Fin k → Bool) (z : Fin k → Sigma X)
    (j : Fin k) (hj : s j = true) (hz : coordinateUnionWeight μ (z j) = 0) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k s (productANOVATensor μ k base f) z = 0 := by
  apply finiteSectionL2Norm_eq_zero_of_fixed _ k s _ z j hj
  intro v hv
  apply productANOVATensor_zero_of_zero_weight μ k base f v j
  rw [hv, hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_moment_expansion (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q) =
      ∑ a : (Fin q × Fin k) → I, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) := by
  have h := (FiniteProbabilityWeights.pi μ).mean_congr_on_support
    (f := fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)
    (g := fun x => (∑ a : Fin k → I,
      productANOVATensor μ k base f (fun j => ⟨a j, x (a j)⟩)) ^ q)
    (fun x hx => congrArg (fun t : ℝ => t ^ q) (productANOVATensor_sum_evaluate μ k base f x hx).symm)
  rw [h]
  simp_rw [Fintype.sum_pow]
  rw [FiniteProbabilityWeights.mean_sum]
  exact Fintype.sum_equiv (Equiv.curry (Fin q) (Fin k) I).symm _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_mean_product (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : (Fin q × Fin k) → I)
    (horder : ∀ j, StrictMono (fun l => a (j, l))) :
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) =
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, productANOVA μ (Finset.univ.image (fun l => a (j, l))) f x) := by
  apply FiniteProbabilityWeights.mean_congr_on_support
  intro x hx
  apply Finset.prod_congr rfl
  intro j _
  rw [productANOVATensor_evaluate μ k base f (fun l => a (j, l)) x hx, ite_eq_left (horder j)]

theorem productANOVATensor_mean_zero_of_not_ordered (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : (Fin q × Fin k) → I) (j : Fin q)
    (hj : ¬ StrictMono (fun l => a (j, l))) :
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ b, productANOVATensor μ k base f (fun l => ⟨a (b, l), x (a (b, l))⟩)) = 0 := by
  have he : (fun x : ∀ i, X i => ∏ b, productANOVATensor μ k base f
      (fun l => ⟨a (b, l), x (a (b, l))⟩)) = fun _ => 0 := by
    funext x
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (productANOVATensor_zero_of_not_ordered μ k base f _ hj)
  rw [he, FiniteProbabilityWeights.mean_const]

theorem productANOVATensor_mean_zero_of_singleton (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : (Fin q × Fin k) → I)
    (horder : ∀ j, StrictMono (fun l => a (j, l))) (i : I)
    (hi : (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card = 1) :
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) = 0 := by
  rw [productANOVATensor_mean_product μ k q base f a horder]
  apply productANOVA_term_zero_of_singleton_count μ
    (fun j => Finset.univ.image (fun l => a (j, l))) (fun _ => f) (fun j => j) i
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hi

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

noncomputable def productANOVATensorChoices (k q : ℕ) : Finset ((Fin q × Fin k) → I) := by
  classical
  exact Finset.univ.filter (fun a => (∀ j, StrictMono (fun l => a (j, l))) ∧
    ∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1)

theorem mem_productANOVATensorChoices (k q : ℕ) (a : (Fin q × Fin k) → I) :
    a ∈ productANOVATensorChoices k q ↔ (∀ j, StrictMono (fun l => a (j, l))) ∧
      ∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1 := by
  classical
  simp only [productANOVATensorChoices, Finset.mem_filter, Finset.mem_univ, true_and]

variable {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_moment_admissible (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q) =
      ∑ a ∈ productANOVATensorChoices k q, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)) := by
  classical
  rw [productANOVATensor_moment_expansion μ k q base f]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a _ ha
  by_cases horder : ∀ j, StrictMono (fun l => a (j, l))
  · have hs : ¬∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1 := by
      intro hs
      exact ha ((mem_productANOVATensorChoices k q a).mpr ⟨horder, hs⟩)
    push Not at hs
    obtain ⟨i, hi⟩ := hs
    exact productANOVATensor_mean_zero_of_singleton μ k q base f a horder i hi
  · push Not at horder
    obtain ⟨j, hj⟩ := horder
    exact productANOVATensor_mean_zero_of_not_ordered μ k q base f a j hj

theorem productANOVATensor_abs_moment_le (k q : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    |(FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)| ≤
      ∑ a ∈ productANOVATensorChoices k q, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, |productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩)|) := by
  rw [productANOVATensor_moment_admissible μ k q base f]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simpa only [Finset.abs_prod] using (FiniteProbabilityWeights.pi μ).abs_mean_le_mean_abs
    (fun x => ∏ j, productANOVATensor μ k base f (fun l => ⟨a (j, l), x (a (j, l))⟩))

end Erdos3

end

end OAI
