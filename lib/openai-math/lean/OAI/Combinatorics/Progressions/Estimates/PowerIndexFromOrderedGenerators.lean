import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import OAI.Combinatorics.Progressions.Estimates.PowerSubgroup
import OAI.Combinatorics.Progressions.Linear.OrderedBasisCoordinates

namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G] {d : ℕ}

def orderedGroupTailProduct (a : Fin d → G) (i : ℕ) : G :=
  (((List.finRange d).drop i).map a).prod

def orderedGroupProduct (a : Fin d → G) : G := orderedGroupTailProduct a 0

def orderedZpowProduct (a : Fin d → G) (z : Fin d → ℤ) : G :=
  orderedGroupProduct (fun j => a j ^ z j)

theorem orderedGroupTailProduct_terminal (a : Fin d → G) {i : ℕ} (hi : d ≤ i) :
    orderedGroupTailProduct a i = 1 := by
  simp only [orderedGroupTailProduct,
    List.drop_eq_nil_of_le (as := List.finRange d) (i := i) (by simpa using hi),
    List.map_nil, List.prod_nil]

theorem orderedGroupTailProduct_step (a : Fin d → G) (j : Fin d) :
    orderedGroupTailProduct a j.val = a j * orderedGroupTailProduct a (j.val + 1) := by
  unfold orderedGroupTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem orderedGroupTailProduct_congr (i : ℕ) {a b : Fin d → G}
    (h : ∀ j : Fin d, i ≤ j.val → a j = b j) :
    orderedGroupTailProduct a i = orderedGroupTailProduct b i := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  exact h j (mem_drop_finRange_iff.mp hj)

theorem orderedGroupProduct_map {H : Type*} [Group H] (f : G →* H) (a : Fin d → G) :
    f (orderedGroupProduct a) = orderedGroupProduct (fun j => f (a j)) := by
  simp only [orderedGroupProduct, orderedGroupTailProduct, List.drop_zero,
    map_list_prod, List.map_map, Function.comp_def]

theorem orderedZpowProduct_map {H : Type*} [Group H] (f : G →* H)
    (a : Fin d → G) (z : Fin d → ℤ) :
    f (orderedZpowProduct a z) = orderedZpowProduct (fun j => f (a j)) z := by
  simp only [orderedZpowProduct, orderedGroupProduct_map, map_zpow]

theorem orderedZpowProduct_mem (Γ : Subgroup G) (a : Fin d → G)
    (ha : ∀ j, a j ∈ Γ) (z : Fin d → ℤ) : orderedZpowProduct a z ∈ Γ := by
  apply list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact Γ.zpow_mem (ha j) _

theorem exists_bounded_ordered_exponents (a : Fin d → G) (m : ℕ) (hm : 0 < m)
    (ha : ∀ j, a j ^ m = 1) (z : Fin d → ℤ) :
    ∃ r : Fin d → Fin m, orderedGroupProduct (fun j => a j ^ (r j).val) =
      orderedZpowProduct a z := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hnonneg (j : Fin d) : 0 ≤ z j % (m : ℤ) := Int.emod_nonneg _ (ne_of_gt hmz)
  let r : Fin d → Fin m := fun j => ⟨(z j % (m : ℤ)).toNat, by
    have hlt := Int.emod_lt_of_pos (z j) hmz
    omega⟩
  refine ⟨r, ?_⟩
  unfold orderedZpowProduct
  apply congrArg orderedGroupProduct
  funext j
  rw [zpow_eq_zpow_emod' (z j) (ha j)]
  change a j ^ (z j % (m : ℤ)).toNat = a j ^ (z j % (m : ℤ))
  rw [← zpow_natCast, Int.toNat_of_nonneg (hnonneg j)]

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [Group G] {d : ℕ}

theorem powerSubgroup_index_le_of_ordered_generators (a : Fin d → G)
    (hgen : Function.Surjective (orderedZpowProduct a)) (m : ℕ) (hm : 0 < m) :
    (powerSubgroup G m).FiniteIndex ∧ (powerSubgroup G m).index ≤ m ^ d := by
  let Q := G ⧸ powerSubgroup G m
  let q : G →* Q := QuotientGroup.mk' _
  let f : (Fin d → Fin m) → Q := fun r => orderedGroupProduct (fun j => q (a j) ^ (r j).val)
  have hpow (j : Fin d) : q (a j) ^ m = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pow_mem_powerSubgroup (a j) m)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, rfl⟩ := hgen g
    obtain ⟨r, hr⟩ := exists_bounded_ordered_exponents (fun j => q (a j)) m hm hpow z
    refine ⟨r, ?_⟩
    change orderedGroupProduct (fun j => q (a j) ^ (r j).val) = q (orderedZpowProduct a z)
    rw [orderedZpowProduct_map]
    exact hr
  let : Finite Q := Finite.of_surjective f hf
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  change Nat.card Q ≤ m ^ d
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using
    Nat.card_le_card_of_surjective f hf

end Erdos3

end

end OAI
