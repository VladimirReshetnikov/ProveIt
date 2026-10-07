import OAI.Combinatorics.Progressions.Geometry.ProductTupleSupport
import OAI.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound

namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def finiteFixedTagSet (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X) : Finset I :=
  Finset.univ.image (fun i : {i : Fin n // s i = true} => (z i).1)

theorem finiteSectionFill_tagSet (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X) :
    Finset.univ.image (fun i => (finiteSectionFill n s z v i).1) =
      finiteFixedTagSet n s z ∪ Finset.univ.image (fun i => (v i).1) := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    by_cases hi : s i = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by rw [finiteSectionFill_fixed n s z v i hi]⟩
    · apply Finset.mem_union_right
      let j := (finiteSectionFreeOrder n s).symm ⟨i, hi⟩
      have he : (finiteSectionFreeOrder n s j : Fin n) = i :=
        congrArg Subtype.val ((finiteSectionFreeOrder n s).apply_symm_apply ⟨i, hi⟩)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [← he, finiteSectionFill_free]⟩
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [finiteSectionFill_fixed n s z v i i.property]⟩
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨finiteSectionFreeOrder n s j, Finset.mem_univ _, by rw [finiteSectionFill_free]⟩

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [LinearOrder I] {X : I → Type*}

theorem finiteSectionFill_free_strictMono (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X)
    (h : StrictMono (fun i => (finiteSectionFill n s z v i).1)) :
    StrictMono (fun i => (v i).1) := by
  intro i j hij
  have he : (finiteSectionFreeOrder n s i : Fin n) < finiteSectionFreeOrder n s j :=
    (finiteSectionFreeOrder n s).strictMono hij
  simpa only [finiteSectionFill_free] using h he

theorem finiteSectionFill_fixed_injective (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X)
    (h : StrictMono (fun i => (finiteSectionFill n s z v i).1)) :
    Function.Injective (fun i : {i : Fin n // s i = true} => (z i).1) := by
  intro i j hij
  apply Subtype.ext
  apply h.injective
  simpa only [finiteSectionFill_fixed n s z v i i.property,
    finiteSectionFill_fixed n s z v j j.property] using hij

theorem finiteSectionFill_tags_disjoint (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X)
    (h : StrictMono (fun i => (finiteSectionFill n s z v i).1)) :
    Disjoint (finiteFixedTagSet n s z) (Finset.univ.image (fun i => (v i).1)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
  have he : (i : Fin n) = finiteSectionFreeOrder n s j := by
    apply h.injective
    simpa only [finiteSectionFill_fixed n s z v i i.property, finiteSectionFill_free] using hi.trans hj.symm
  exact (finiteSectionFreeOrder n s j).property (he ▸ i.property)

theorem finiteFixedTagSet_card (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (hinj : Function.Injective (fun i : {i : Fin n // s i = true} => (z i).1)) :
    (finiteFixedTagSet n s z).card = finiteSectionCount s := by
  rw [finiteFixedTagSet, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    finiteSectionCount_eq_card]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem exists_positive_sectionAnchor (μ : ∀ i, FiniteProbabilityWeights (X i))
    (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (hinj : Function.Injective (fun i : {i : Fin n // s i = true} => (z i).1))
    (hz : ∀ i, s i = true → coordinateUnionWeight μ (z i) ≠ 0) :
    ∃ a : ∀ i, X i, (FiniteProbabilityWeights.pi μ).weight a ≠ 0 ∧
      ∀ i : {i : Fin n // s i = true}, a (z i).1 = (z i).2 := by
  apply exists_positive_productTuplePoint μ _ hinj (fun i => (z i).2)
  change (∏ i : {i : Fin n // s i = true}, coordinateUnionWeight μ (z i)) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz i i.property)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_filled_sq_le (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → Sigma X) (base a : ∀ i, X i) (f : (∀ i, X i) → ℝ)
    (ha : ∀ i : {i : Fin n // s i = true}, a (z i).1 = (z i).2)
    (v : Fin (n - finiteSectionCount s) → Sigma X) :
    productANOVATensor μ n base f (finiteSectionFill n s z v) ^ 2 ≤
      productANOVASectionTensor μ (finiteFixedTagSet n s z) (n - finiteSectionCount s) a base f v ^ 2 := by
  classical
  have transport (x : ∀ i, X i) (u w : Sigma X) (h : u = w)
      (hu : x u.1 = u.2) : x w.1 = w.2 := by
    cases h
    exact hu
  by_cases ho : StrictMono (fun i => (finiteSectionFill n s z v i).1)
  · have hv := finiteSectionFill_free_strictMono n s z v ho
    have hd := finiteSectionFill_tags_disjoint n s z v ho
    by_cases hw : (∏ i, coordinateUnionWeight μ (finiteSectionFill n s z v i)) = 0
    · have he : productANOVATensor μ n base f (finiteSectionFill n s z v) = 0 := by
        simp only [productANOVATensor, ho, dite_true, hw, ite_true]
      rw [he, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · have he : productANOVATensor μ n base f (finiteSectionFill n s z v) =
          productANOVASectionTensor μ (finiteFixedTagSet n s z) (n - finiteSectionCount s) a base f v := by
        simp only [productANOVATensor, ho, dite_true, hw, ite_false,
          productANOVASectionTensor, orderedFamilyTensor, hv, hd, ite_true]
        rw [finiteSectionFill_tagSet]
        apply productANOVA_depends μ _ f
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
          have hj : (z j).1 ∈ finiteFixedTagSet n s z :=
            Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
          simp only [productCoordinateMix, hj, ite_true]
          have he := productTuplePoint_apply (fun i => (finiteSectionFill n s z v i).1)
            ho.injective (fun i => (finiteSectionFill n s z v i).2) base j
          have he' : productTuplePoint (fun i => (finiteSectionFill n s z v i).1)
              ho.injective (fun i => (finiteSectionFill n s z v i).2) base (z j).1 = (z j).2 := by
            exact transport _ _ _ (finiteSectionFill_fixed n s z v j j.property) he
          exact he'.trans (ha j).symm
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
          have hj : (v j).1 ∉ finiteFixedTagSet n s z := fun h =>
            Finset.disjoint_left.mp hd h (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
          simp only [productCoordinateMix, hj, ite_false]
          have he := productTuplePoint_apply (fun i => (finiteSectionFill n s z v i).1)
            ho.injective (fun i => (finiteSectionFill n s z v i).2) base (finiteSectionFreeOrder n s j)
          have he' : productTuplePoint (fun i => (finiteSectionFill n s z v i).1)
              ho.injective (fun i => (finiteSectionFill n s z v i).2) base (v j).1 = (v j).2 := by
            exact transport _ _ _ (finiteSectionFill_free n s z v j) he
          exact he'.trans (productTuplePoint_apply _ hv.injective (fun i => (v i).2) base j).symm
      exact le_of_eq (congrArg (fun x : ℝ => x ^ 2) he)
  · rw [productANOVATensor_zero_of_not_ordered μ n base f _ ho, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

end Erdos3

end

end OAI
