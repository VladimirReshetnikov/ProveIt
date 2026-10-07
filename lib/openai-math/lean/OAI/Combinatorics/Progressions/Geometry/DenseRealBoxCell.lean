import Mathlib
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem card_image_eq_of_same_fibers {α β γ : Type*} [Nonempty α]
    [DecidableEq β] [DecidableEq γ] (A : Finset α) (f : α → β) (g : α → γ)
    (hrel : ∀ x ∈ A, ∀ y ∈ A, f x = f y ↔ g x = g y) :
    (A.image f).card = (A.image g).card := by
  classical
  let r := Function.invFunOn f (A : Set α)
  have hr {y : β} (hy : y ∈ A.image f) : r y ∈ A ∧ f (r y) = y :=
    Function.invFunOn_pos (Finset.mem_image.mp hy)
  have hinj : Set.InjOn (g ∘ r) (A.image f : Set β) := by
    intro y hy z hz h
    have he := (hrel (r y) (hr hy).1 (r z) (hr hz).1).mpr h
    simpa only [(hr hy).2, (hr hz).2] using he
  have himage : (A.image f).image (g ∘ r) = A.image g := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨r y, (hr hy).1, rfl⟩
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hfx : f x ∈ A.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨f x, hfx,
        (hrel (r (f x)) (hr hfx).1 x hx).mp (hr hfx).2⟩
  rw [← himage, Finset.card_image_of_injOn hinj]

theorem card_difference_image_of_freiman {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (f : G → H)
    (hf : IsAddFreimanIso 2 (A : Set G) (A.image f : Set H) f) :
    ((A.image f - A.image f).card : ℕ) = (A - A).card := by
  have hrel : ∀ x ∈ A ×ˢ A, ∀ y ∈ A ×ˢ A,
      x.1 - x.2 = y.1 - y.2 ↔ f x.1 - f x.2 = f y.1 - f y.2 := by
    intro x hx y hy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    rw [sub_eq_sub_iff_add_eq_add, sub_eq_sub_iff_add_eq_add]
    exact (hf.add_eq_add hx1 hy2 hy1 hx2).symm
  have hcard := card_image_eq_of_same_fibers (A ×ˢ A)
    (fun x => x.1 - x.2) (fun x => f x.1 - f x.2) hrel
  have hout : (A ×ˢ A).image (fun x => f x.1 - f x.2) = A.image f - A.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      exact Finset.mem_sub.mpr ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
    · intro hz
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩,
        by change f x - f y = z; rw [hxu, hyv]; exact huv⟩
  simpa only [hout, Finset.image_sub_product] using hcard.symm

theorem exists_nonempty_large_fiber {α β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (A : Finset α) (hA : A.Nonempty) (f : α → β) :
    ∃ b : β, (A.filter fun x => f x = b).Nonempty ∧
      A.card ≤ Fintype.card β * (A.filter fun x => f x = b).card := by
  classical
  let k := Fintype.card β
  have hk : 0 < k := Fintype.card_pos
  let n := (A.card - 1) / k
  have hApos := hA.card_pos
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨b, _, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _)
      (by simpa only [Finset.card_univ] using hkn)
  refine ⟨b, Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard), ?_⟩
  have hceil : A.card - 1 < k * (n + 1) := Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤ k * (A.filter fun x => f x = b).card :=
    Nat.mul_le_mul_left k (by omega)
  change A.card ≤ k * (A.filter fun x => f x = b).card
  omega

end Erdos3.FreimanModel

end

section

namespace Erdos3

noncomputable def realBoxCellCount (C : ℝ) (q : ℕ) : ℕ := ⌊2 * q * C⌋₊ + 1

theorem realBoxCellCount_pos (C : ℝ) (q : ℕ) : 0 < realBoxCellCount C q := by
  unfold realBoxCellCount
  omega

theorem realBoxCellCount_le {C : ℝ} (hC : 0 ≤ C) (q : ℕ) :
    (realBoxCellCount C q : ℝ) ≤ 2 * q * C + 1 := by
  unfold realBoxCellCount
  push_cast
  exact add_le_add (Nat.floor_le (by positivity)) (le_refl 1)

theorem realBoxCell_floor_lt {C : ℝ} (q : ℕ) (y : ℝ) (hy : |y| ≤ C) :
    ⌊(q : ℝ) * (y + C)⌋₊ < realBoxCellCount C q := by
  have hupper : (q : ℝ) * (y + C) ≤ 2 * q * C := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 (Nat.cast_nonneg (α := ℝ) q)
    nlinarith
  exact Nat.lt_succ_of_le (Nat.floor_mono hupper)

noncomputable def realBoxCellCenter (C : ℝ) (q n : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) / q - C

theorem realBoxCell_offset {C : ℝ} (q : ℕ) (hq : 0 < q) (y : ℝ) (hy : |y| ≤ C) :
    |y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊| ≤ (1 / 2 : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnonneg : 0 ≤ (q : ℝ) * (y + C) := by
    exact mul_nonneg hqR.le (by linarith [(abs_le.mp hy).1])
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((q : ℝ) * (y + C))
  have he : (q : ℝ) * (y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊) =
      (q : ℝ) * (y + C) - (⌊(q : ℝ) * (y + C)⌋₊ + (1 / 2 : ℝ)) := by
    unfold realBoxCellCenter
    field_simp
    ring
  apply (le_div_iff₀ hqR).mpr
  calc
    _ = |(q : ℝ) * (y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊)| := by
      rw [abs_mul, abs_of_pos hqR]
      ring
    _ ≤ _ := by rw [he]; apply abs_le.mpr; constructor <;> linarith

theorem exists_dense_real_box_cell {ι α : Type} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (y : α → ι → ℝ)
    {C : ℝ} (hbound : ∀ a ∈ S, ∀ i, |y a i| ≤ C)
    (q : ℕ) (hq : 0 < q) :
    ∃ T ⊆ S, T.Nonempty ∧ S.card ≤ realBoxCellCount C q ^ Fintype.card ι * T.card ∧
      ∃ c : ι → ℝ, (∀ i, |c i| ≤ C + (1 / 2 : ℝ) / q) ∧
        ∀ a ∈ T, ∀ i, |y a i - c i| ≤ (1 / 2 : ℝ) / q := by
  classical
  let m := realBoxCellCount C q
  have hm : 0 < m := realBoxCellCount_pos C q
  let : NeZero m := ⟨hm.ne'⟩
  let label (a : α) (i : ι) : Fin m :=
    ⟨⌊(q : ℝ) * (y a i + C)⌋₊ % m, Nat.mod_lt _ hm⟩
  obtain ⟨b, hT, hcard⟩ := FreimanModel.exists_nonempty_large_fiber S hS label
  let T := S.filter (fun a => label a = b)
  let c : ι → ℝ := fun i => realBoxCellCenter C q (b i).val
  have hclose : ∀ a ∈ T, ∀ i, |y a i - c i| ≤ (1 / 2 : ℝ) / q := by
    intro a ha i
    have haS := (Finset.mem_filter.mp ha).1
    have he := congrArg Fin.val (congrFun (Finset.mem_filter.mp ha).2 i)
    change ⌊(q : ℝ) * (y a i + C)⌋₊ % m = (b i).val at he
    rw [Nat.mod_eq_of_lt (realBoxCell_floor_lt q (y a i) (hbound a haS i))] at he
    dsimp only [c]
    rw [← he]
    exact realBoxCell_offset q hq (y a i) (hbound a haS i)
  refine ⟨T, Finset.filter_subset _ _, hT, ?_, c, ?_, hclose⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
  · obtain ⟨a, ha⟩ := hT
    intro i
    calc
      |c i| = |y a i - (y a i - c i)| := by congr 1; ring
      _ ≤ |y a i| + |y a i - c i| := abs_sub _ _
      _ ≤ C + (1 / 2 : ℝ) / q := add_le_add
        (hbound a (Finset.mem_filter.mp ha).1 i) (hclose a ha i)

end Erdos3

end

end OAI
