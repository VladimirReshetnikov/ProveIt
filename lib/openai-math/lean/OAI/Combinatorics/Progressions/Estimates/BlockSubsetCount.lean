import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype σ] [DecidableEq ι] [DecidableEq σ]

def blockSubsetUnion (f : σ → Finset ι) : Finset ι := Finset.univ.biUnion f

omit [DecidableEq σ] in
theorem blockSubsetUnion_subset (f : σ → Finset ι) (S : Finset ι)
    (h : ∀ i, f i ⊆ S) : blockSubsetUnion f ⊆ S := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact h i hi

theorem blockSubsetUnion_filter (π : ι → σ) (f : σ → Finset ι)
    (h : ∀ i, ∀ x ∈ f i, π x = i) (i : σ) :
    (blockSubsetUnion f).filter (fun x => π x = i) = f i := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    have hji : j = i := (h j x hj).symm.trans hxi
    exact hji ▸ hj
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩, h i x hx⟩

theorem blockSubsetUnion_filters (π : ι → σ) (S : Finset ι) :
    blockSubsetUnion (fun i => S.filter fun x => π x = i) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hi).1
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨π x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype σ] [DecidableEq ι] [DecidableEq σ]

noncomputable def blockSubsetEquiv (π : ι → σ) (S : Finset ι) (a : σ → ℕ) :
    {T : Finset ι // T ⊆ S ∧ ∀ i, (T.filter fun j => π j = i).card = a i} ≃
      (∀ i, {T : Finset ι // T ∈ (S.filter fun j => π j = i).powersetCard (a i)}) where
  toFun T i := ⟨T.val.filter (fun j => π j = i), Finset.mem_powersetCard.mpr ⟨by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨T.property.1 (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩,
    T.property.2 i⟩⟩
  invFun f := ⟨blockSubsetUnion (fun i => (f i).val), by
    have hf : ∀ i, (f i).val ⊆ S.filter (fun j => π j = i) :=
      fun i => (Finset.mem_powersetCard.mp (f i).property).1
    refine ⟨blockSubsetUnion_subset _ S (fun i j hj => (Finset.mem_filter.mp (hf i hj)).1), ?_⟩
    intro i
    rw [blockSubsetUnion_filter π _ (fun i j hj => (Finset.mem_filter.mp (hf i hj)).2)]
    exact (Finset.mem_powersetCard.mp (f i).property).2⟩
  left_inv T := Subtype.ext (blockSubsetUnion_filters π T.val)
  right_inv f := by
    funext i
    apply Subtype.ext
    exact blockSubsetUnion_filter π _
      (fun i j hj => (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (f i).property).1 hj)).2) i

theorem card_blockSubsets [Fintype ι] (π : ι → σ) (S : Finset ι) (a : σ → ℕ) :
    Fintype.card {T : Finset ι // T ⊆ S ∧ ∀ i, (T.filter fun j => π j = i).card = a i} =
      ∏ i, ((S.filter fun j => π j = i).card).choose (a i) := by
  classical
  rw [Fintype.card_congr (blockSubsetEquiv π S a), Fintype.card_pi]
  simp only [Fintype.card_coe, Finset.card_powersetCard]

end Erdos3

end

end OAI
