import Mathlib

namespace OAI

section

section BSGIndicatorNotation

scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]

end BSGIndicatorNotation

section BSGIndicatorAlgebra

open scoped Indicator

variable {F α β M₀ N₀ : Type*}

namespace Set
open scoped _root_.Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

lemma indicator_one_inter_apply (s t : Set α) (x : α) : 𝟭_[s ∩ t, M₀] x = 𝟭_[s] x * 𝟭_[t] x := by
  classical simp [_root_.Set.indicator_apply, ← ite_and, and_comm]

lemma indicator_one_inter (s t : Set α) : 𝟭_[s ∩ t, M₀] = 𝟭_[s] * 𝟭_[t] :=
  funext <| indicator_one_inter_apply _ _

lemma map_indicator_one [FunLike F M₀ N₀] [MonoidWithZeroHomClass F M₀ N₀] (f : F) (s : Set α)
    (x : α) : f (𝟭_[s] x) = 𝟭_[s] x := by classical exact MonoidWithZeroHom.map_ite_one_zero ..

variable (M₀) in
@[simp] lemma indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    𝟭_[e '' s, M₀] b = 𝟭_[s] (e.symm b) := by classical simp [_root_.Set.indicator_apply]

variable [Nontrivial M₀] {a : α}

@[simp high] lemma indicator_one_apply_eq_zero : 𝟭_[s, M₀] a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff

lemma indicator_one_apply_ne_zero : 𝟭_[s, M₀] a ≠ 0 ↔ a ∈ s := by
  classical exact one_ne_zero.ite_ne_right_iff

@[simp high] lemma indicator_one_eq_zero : 𝟭_[s, M₀] = 0 ↔ s = ∅ := by
  simp [funext_iff, _root_.Set.eq_empty_iff_forall_notMem]

lemma indicator_one_ne_zero : 𝟭_[s, M₀] ≠ 0 ↔ s.Nonempty := by simp [_root_.Set.nonempty_iff_ne_empty]

variable (M₀) in
@[simp high] lemma support_indicator_one : 𝟭_[s, M₀].support = s := by
  ext; exact indicator_one_apply_ne_zero

end Set

end BSGIndicatorAlgebra

section BSGIndicatorOrder

open scoped Indicator

namespace Set
open scoped _root_.Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  _root_.Set.indicator_nonneg (by simp)

@[simp] lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[simp]
lemma indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [_root_.Set.indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
end Set

end BSGIndicatorOrder

section BSGIndicatorStar

open scoped ComplexConjugate Indicator

namespace Set
open scoped _root_.Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp] lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [_root_.Set.indicator_apply]

@[simp] lemma conj_indicator_one (s : Set α) : conj 𝟭_[s, R] = 𝟭_[s] := by ext; simp

end Set

end BSGIndicatorStar

end

end OAI
