import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.SplitIfs

/-! Every nonempty proper cardinality in a finite cyclic group realizes
every prescribed sum. No coprimality or primality assumption is needed. -/
namespace AdditionalSimplifications.RestrictedSubsetSums

set_option Elab.async false

open scoped BigOperators

/-- A sorted list of a points: shift every point by q and the last r by one. -/
def staircase (a q r i : ℕ) : ℕ := i + q + if a - r ≤ i then 1 else 0

theorem staircase_strictMono (a q r : ℕ) : StrictMono (staircase a q r) := by
  intro i j hij
  dsimp only [staircase]
  split_ifs <;> omega

theorem suffix_ones {a r : ℕ} (hr : r ≤ a) :
    (∑ i ∈ Finset.range a, if a - r ≤ i then 1 else 0) = r := by
  have hf : (Finset.range a).filter (fun i => a - r ≤ i) = Finset.Ico (a-r) a := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.card_filter, hf, Nat.card_Ico]
  omega

theorem staircase_sum {a q r : ℕ} (hr : r ≤ a) :
    (∑ i ∈ Finset.range a, staircase a q r i) =
      (∑ i ∈ Finset.range a, i) + a*q + r := by
  simp only [staircase, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  rw [suffix_ones hr]

theorem staircase_lt {T a q r i : ℕ} (ha : a ≤ T) (hi : i < a)
    (hq : q ≤ T-a) (htop : q = T-a → r = 0) : staircase a q r i < T := by
  dsimp only [staircase]
  split_ifs with h
  · have hq' : q < T-a := by
      have hne : q ≠ T-a := by intro he; have := htop he; omega
      omega
    omega
  · omega

/-- Exact interval of sums of a-subsets of [0,T), with an explicit staircase. -/
theorem exists_nat_subset_sum {T a d : ℕ} (ha : 0 < a) (haT : a ≤ T)
    (hd : d ≤ a*(T-a)) :
    ∃ s : Finset ℕ, s ⊆ Finset.range T ∧ s.card = a ∧
      (∑ x ∈ s, x) = (∑ i ∈ Finset.range a, i) + d := by
  let q := d/a
  let r := d%a
  have hr : r < a := Nat.mod_lt _ ha
  have hdecomp : r + a*q = d := Nat.mod_add_div _ _
  have hq : q ≤ T-a := Nat.le_of_mul_le_mul_left (by omega : a*q ≤ a*(T-a)) ha
  have htop : q = T-a → r = 0 := by intro h; rw [h] at hdecomp; omega
  let s := (Finset.range a).image (staircase a q r)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (staircase_lt haT (Finset.mem_range.mp hi) hq htop)
  · dsimp only [s]
    rw [Finset.card_image_of_injective _ (staircase_strictMono a q r).injective,
      Finset.card_range]
  · dsimp only [s]
    rw [Finset.sum_image (fun _ _ _ _ h => (staircase_strictMono a q r).injective h),
      staircase_sum hr.le]
    omega

/-- The integer interval of sums spans a complete residue interval. -/
theorem window_covers_modulus {T a : ℕ} (ha : 0 < a) (haT : a < T) :
    T-1 ≤ a*(T-a) := by
  have hm := Nat.mul_le_mul_left (a-1) (show 1 ≤ T-a by omega)
  have he : a*(T-a) = (a-1)*(T-a)+(T-a) := by
    calc
      a*(T-a) = ((a-1)+1)*(T-a) := congrArg (fun x => x*(T-a)) (by omega)
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Surjectivity of the fixed-cardinality subset-sum map on a cyclic group. -/
theorem exists_subset_card_sum {T a : ℕ} (ha : 0 < a) (haT : a < T)
    (u : ZMod T) : ∃ s : Finset (ZMod T), s.card = a ∧ (∑ x ∈ s, x) = u := by
  letI : NeZero T := ⟨by omega⟩
  let σ : ℕ := ∑ i ∈ Finset.range a, i
  let d : ℕ := (u-(σ : ZMod T)).val
  have hd : d ≤ a*(T-a) :=
    (Nat.le_pred_of_lt (ZMod.val_lt (u-(σ : ZMod T)))).trans (window_covers_modulus ha haT)
  obtain ⟨s, hs, hcard, hsum⟩ := exists_nat_subset_sum ha haT.le hd
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod T)) s := by
    intro x hx y hy he
    have hxT := Finset.mem_range.mp (hs hx)
    have hyT := Finset.mem_range.mp (hs hy)
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt hxT, ZMod.val_natCast_of_lt hyT] using hv
  refine ⟨s.image (fun x : ℕ => (x : ZMod T)), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · rw [Finset.sum_image hinj, ← Nat.cast_sum, hsum, Nat.cast_add]
    change (σ : ZMod T) + (d : ZMod T) = u
    rw [show (d : ZMod T) = u-(σ : ZMod T) from ZMod.natCast_zmod_val _]
    rw [add_comm, sub_add_cancel]

-- A nonunit cardinality, which the old coprime-length interface cannot handle.
example (u : ZMod 4) : ∃ s : Finset (ZMod 4), s.card = 2 ∧ (∑ x ∈ s, x) = u :=
  exists_subset_card_sum (by decide) (by decide) u

-- The same theorem works over a composite modulus with noncoprime cardinality.
example (u : ZMod 12) : ∃ s : Finset (ZMod 12), s.card = 8 ∧ (∑ x ∈ s, x) = u :=
  exists_subset_card_sum (by decide) (by decide) u

#print axioms exists_nat_subset_sum
#print axioms exists_subset_card_sum

end AdditionalSimplifications.RestrictedSubsetSums
