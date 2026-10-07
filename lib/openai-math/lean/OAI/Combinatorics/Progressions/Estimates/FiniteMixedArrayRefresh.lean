import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic

namespace OAI

section

namespace Erdos3

variable {A B J K C V S T U W : Type*}

def mixedArrayEmbedding (e : A ↪ J) (d : B ↪ K) : A ⊕ B ↪ J ⊕ (K ⊕ C) where
  toFun := Sum.elim (fun a => Sum.inl (e a)) (fun b => Sum.inr (Sum.inl (d b)))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (d.injective (Sum.inl.inj (Sum.inr.inj h)))

@[simp] theorem mixedArrayEmbedding_inl (e : A ↪ J) (d : B ↪ K) (a : A) :
    mixedArrayEmbedding (C := C) e d (Sum.inl a) = Sum.inl (e a) := rfl

@[simp] theorem mixedArrayEmbedding_inr (e : A ↪ J) (d : B ↪ K) (b : B) :
    mixedArrayEmbedding (C := C) e d (Sum.inr b) = Sum.inr (Sum.inl (d b)) := rfl

theorem mixedArray_extend (e : A ↪ J) (d : B ↪ K)
    (xs : A → V) (xd : B → V) (fs : J → V) (fd : K → V) (fc : C → V) :
    Sum.elim (Function.extend e xs fs) (Sum.elim (Function.extend d xd fd) fc) =
      Function.extend (mixedArrayEmbedding e d) (Sum.elim xs xd)
        (Sum.elim fs (Sum.elim fd fc)) := by
  classical
  funext x
  cases x with
  | inl j =>
    by_cases hj : ∃ a, e a = j
    · obtain ⟨a, rfl⟩ := hj
      exact (e.injective.extend_apply xs fs a).trans
        ((mixedArrayEmbedding (C := C) e d).injective.extend_apply
          (Sum.elim xs xd) (Sum.elim fs (Sum.elim fd fc)) (Sum.inl a)).symm
    · have hnone : ¬ ∃ x, mixedArrayEmbedding (C := C) e d x = Sum.inl j := by
        rintro ⟨a | b, h⟩
        · exact hj ⟨a, Sum.inl.inj h⟩
        · cases h
      simp only [Sum.elim_inl, Function.extend_apply' _ _ _ hj,
        Function.extend_apply' _ _ _ hnone]
  | inr x =>
    cases x with
    | inl k =>
      by_cases hk : ∃ b, d b = k
      · obtain ⟨b, rfl⟩ := hk
        exact (d.injective.extend_apply xd fd b).trans
          ((mixedArrayEmbedding (C := C) e d).injective.extend_apply
            (Sum.elim xs xd) (Sum.elim fs (Sum.elim fd fc)) (Sum.inr b)).symm
      · have hnone : ¬ ∃ x, mixedArrayEmbedding (C := C) e d x = Sum.inr (Sum.inl k) := by
          rintro ⟨a | b, h⟩
          · cases h
          · exact hk ⟨b, Sum.inl.inj (Sum.inr.inj h)⟩
        simp only [Sum.elim_inr, Sum.elim_inl, Function.extend_apply' _ _ _ hk,
          Function.extend_apply' _ _ _ hnone]
    | inr c =>
      have hnone : ¬ ∃ x, mixedArrayEmbedding (C := C) e d x = Sum.inr (Sum.inr c) := by
        rintro ⟨a | b, h⟩ <;> cases h
      simp only [Function.extend_apply' _ _ _ hnone, Sum.elim_inr]

theorem extend_comp_equiv (p : S ≃ U) (q : T ≃ W) (actual : S ↪ T) (g : U ↪ W)
    (h : ∀ s, q (actual s) = g (p s)) (selected : U → V) (base : W → V) :
    Function.extend g selected base ∘ q =
      Function.extend actual (selected ∘ p) (base ∘ q) := by
  classical
  funext t
  by_cases ht : ∃ s, actual s = t
  · obtain ⟨s, rfl⟩ := ht
    change Function.extend g selected base (q (actual s)) = _
    rw [h, g.injective.extend_apply, actual.injective.extend_apply]
    rfl
  · have hnone : ¬ ∃ u, g u = q t := by
      rintro ⟨u, hu⟩
      apply ht
      refine ⟨p.symm u, q.injective ?_⟩
      rw [h, p.apply_symm_apply, hu]
    change Function.extend g selected base (q t) = _
    rw [Function.extend_apply' _ _ _ hnone, Function.extend_apply' _ _ _ ht]
    rfl

theorem mixedArray_extend_comp_equiv (e : A ↪ J) (d : B ↪ K)
    (p : S ≃ A ⊕ B) (q : T ≃ J ⊕ (K ⊕ C)) (actual : S ↪ T)
    (h : ∀ s, q (actual s) = mixedArrayEmbedding e d (p s))
    (xs : A → V) (xd : B → V) (fs : J → V) (fd : K → V) (fc : C → V) :
    Sum.elim (Function.extend e xs fs) (Sum.elim (Function.extend d xd fd) fc) ∘ q =
      Function.extend actual ((Sum.elim xs xd) ∘ p)
        ((Sum.elim fs (Sum.elim fd fc)) ∘ q) := by
  rw [mixedArray_extend]
  exact extend_comp_equiv p q actual (mixedArrayEmbedding e d) h _ _

theorem map_coordinate_extend (e : A ↪ J) (F : J → V → W)
    (selected : A → V) (fixed : J → V) :
    (fun j => F j (Function.extend e selected fixed j)) =
      Function.extend e (fun a => F (e a) (selected a)) (fun j => F j (fixed j)) := by
  classical
  funext j
  by_cases hj : ∃ a, e a = j
  · obtain ⟨a, rfl⟩ := hj
    rw [e.injective.extend_apply, e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj]

end Erdos3

end

end OAI
