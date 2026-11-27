import GRHArticle.ProgressionFree.IntegerPrefix
import Mathlib.Data.Nat.Periodic

/-!
# Ford's integral-ratio intervals

The construction used in McNew's lower bound places three intervals at each
scale. One interval uses 24 residue classes modulo 60.
Two separated copies improve the finite proportion beyond 0.818410.
See [McNew, Theorem 3.2](https://www.nathanmcnew.com/GPFsets.pdf).
-/

namespace GRHArticle.ProgressionFree

open Finset

private abbrev fordResidue (a : ℕ) : Prop := ¬ 3 ∣ a ∧ ¬ 4 ∣ a ∧ ¬ 5 ∣ a

private theorem fordResidue_periodic : Function.Periodic fordResidue 60 :=
  fun a ↦ propext (by simp only [fordResidue]; omega)

private theorem count_fordResidue (k : ℕ) : Nat.count fordResidue (60*k) = 24*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : Nat.count (fun n ↦ fordResidue (n+60)) (60*k) = Nat.count fordResidue (60*k) := by
      simp only [Nat.count_eq_card_filter_range]
      apply congrArg Finset.card
      exact Finset.filter_congr (fun n _ ↦ (fordResidue_periodic n).to_iff)
    have hnum : Nat.count fordResidue 60 = 24 := by decide
    rw [Nat.mul_succ, Nat.count_add', he, ih, hnum, Nat.mul_succ]

/-- The small interval, the unrestricted top interval, and the residue
classes from the middle interval, with upper cutoff `8640*t`. -/
def integerFordBlock (t : ℕ) : Finset ℕ :=
  Ioc (180*t) (720*t) ∪ Ioc (2160*t) (8640*t) ∪
    ((Ioc (960*t) (1080*t)).filter fordResidue)

private theorem mem_fordBlock {t n : ℕ} : n ∈ integerFordBlock t ↔
    (180*t < n ∧ n ≤ 720*t) ∨ (2160*t < n ∧ n ≤ 8640*t) ∨
      ((960*t < n ∧ n ≤ 1080*t) ∧ fordResidue n) := by
  simp only [integerFordBlock, mem_union, mem_Ioc, mem_filter, or_assoc]

private theorem fordBlock_bounds {n t : ℕ} (h : n ∈ integerFordBlock t) :
    180*t < n ∧ n ≤ 8640*t := by
  rw [mem_fordBlock] at h
  omega

/-- None of Ford's three intervals and residue classes together contains
a nonconstant progression with integral ratio. -/
theorem integerFordBlock_admissible (t : ℕ) :
    IntegerPrefixAdmissible true (integerFordBlock t : Set ℕ) := by
  apply (integerPrefixAdmissible_integral_iff (fun n hn ↦ by have := fordBlock_bounds hn; omega)).mpr
  intro a r hr ha hb hc
  have h₀ := (fordBlock_bounds ha).1
  have h₂ := (fordBlock_bounds hc).2
  have hr' : r ≤ 6 := by
    by_contra! h
    have h₄₉ : 49 ≤ r*r := Nat.mul_le_mul h h
    have hmul := Nat.mul_le_mul_left a h₄₉
    rw [← Nat.mul_assoc] at hmul
    omega
  rw [Finset.mem_coe, mem_fordBlock] at ha hb hc
  simp only [fordResidue] at ha hb hc
  interval_cases r <;> omega

/-- The block cardinality includes the exact number of allowed middle residues. -/
theorem card_integerFordBlock (t : ℕ) : (integerFordBlock t).card = 7068*t := by
  let A := Ioc (180*t) (720*t)
  let B := Ioc (2160*t) (8640*t)
  let C := (Ioc (960*t) (1080*t)).filter fordResidue
  have hAB : Disjoint A B := disjoint_left.mpr (by intro n hn hn'; simp [A,B] at hn hn'; omega)
  have hABC : Disjoint (A∪B) C := disjoint_left.mpr (by
    intro n hn hn'; simp [A,B] at hn; have hx := mem_Ioc.mp (mem_filter.mp hn').1; omega)
  have he : Ioc (960*t) (1080*t) = Ico (960*t+1) ((960*t+1)+60*(2*t)) := by
    ext n; simp only [mem_Ioc, mem_Ico]; omega
  have hp : Function.Periodic fordResidue (60*(2*t)) := by
    intro n
    apply propext
    simp only [fordResidue]
    omega
  have hC : C.card = 24*(2*t) := by
    dsimp [C]
    rw [he, Nat.filter_Ico_card_eq_of_periodic _ _ _ hp, count_fordResidue]
  change ((A∪B)∪C).card = _
  rw [card_union_of_disjoint hABC, card_union_of_disjoint hAB, hC]
  simp only [A,B,Nat.card_Ioc]
  omega

/-- Two Ford blocks with the gap between their occupied intervals. -/
def integerFordDoubleBlock (t : ℕ) : Finset ℕ := integerFordBlock t ∪ integerFordBlock (2304*t)

theorem integerFordDoubleBlock_admissible (t : ℕ) :
    IntegerPrefixAdmissible true (integerFordDoubleBlock t : Set ℕ) := by
  have hbounds (n : ℕ) (hn : n ∈ integerFordDoubleBlock t) :
      180*t < n ∧ n ≤ 8640*(2304*t) := by
    rcases mem_union.mp hn with h|h <;> have := fordBlock_bounds h <;> omega
  apply (integerPrefixAdmissible_integral_iff (fun n hn ↦ by have := hbounds n hn; omega)).mpr
  intro a r hr ha hb hc
  have hf (s : ℕ) := (integerPrefixAdmissible_integral_iff (A := (integerFordBlock s : Set ℕ))
    (fun n hn ↦ by have := fordBlock_bounds hn; omega)).mp (integerFordBlock_admissible s)
  have hab : a ≤ a*r := Nat.le_mul_of_pos_right _ (by omega)
  have hbc : a*r ≤ a*r*r := Nat.le_mul_of_pos_right _ (by omega)
  rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb <;>
    rcases mem_union.mp hc with hc|hc
  all_goals first | exact hf _ a r hr ha hb hc | skip
  all_goals have h₀ := fordBlock_bounds ha; have h₁ := fordBlock_bounds hb; have h₂ := fordBlock_bounds hc
  all_goals try omega
  all_goals by_cases hrs : r < 48
  all_goals first
    | have hh := Nat.mul_le_mul_left a (show r ≤ 48 by omega); omega
    | have hh := Nat.mul_le_mul_left (a*r) (show r ≤ 48 by omega); omega
    | have hh := Nat.mul_le_mul_left a (show 48 ≤ r by omega); omega
    | have hh := Nat.mul_le_mul_left (a*r) (show 48 ≤ r by omega); omega

theorem mem_integerFordDoubleBlock_bounds {n t : ℕ} (hn : n ∈ integerFordDoubleBlock t) :
    0 < n ∧ n ≤ 8640*(2304*t) := by
  rcases mem_union.mp hn with h|h <;> have := fordBlock_bounds h <;> omega

/-- Exact cardinality of the two separated blocks. -/
theorem card_integerFordDoubleBlock (t : ℕ) :
    (integerFordDoubleBlock t).card = 7068 * 2305 * t := by
  have hd : Disjoint (integerFordBlock t) (integerFordBlock (2304*t)) := disjoint_left.mpr (by
    intro n hn hn'; have := fordBlock_bounds hn; have := fordBlock_bounds hn'; omega)
  rw [integerFordDoubleBlock, card_union_of_disjoint hd, card_integerFordBlock, card_integerFordBlock]
  omega

end GRHArticle.ProgressionFree
