/- Modified for ProveIt: use Mathlib v4.32.0's generic prod_le_prod'
for the natural-number product bounds. Mathematical statements unchanged. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def RationalHeightLE (q : ℚ) (H : ℕ) : Prop :=
  q.num.natAbs ≤ H ∧ q.den ≤ H

theorem RationalHeightLE.mono {q : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hHK : H ≤ K) : RationalHeightLE q K :=
  ⟨hq.1.trans hHK, hq.2.trans hHK⟩

theorem rational_fraction_entries_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧
      ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, ha, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc : c ≠ 0 := by
    intro h
    exact hb (by simpa [h] using hd)
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  constructor
  · calc
      _ ≤ c.natAbs * ((a : ℚ) / b).num.natAbs := Nat.le_mul_of_pos_left _ hcpos
      _ = a.natAbs := by simpa only [Int.natAbs_mul] using congrArg Int.natAbs ha.symm
  · calc
      _ ≤ c.natAbs * ((a : ℚ) / b).den := Nat.le_mul_of_pos_left _ hcpos
      _ = b.natAbs := by
        simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hd.symm

theorem rationalHeightLE_fraction (a b : ℤ) (hb : b ≠ 0)
    {H : ℕ} (haH : a.natAbs ≤ H) (hbH : b.natAbs ≤ H) :
    RationalHeightLE ((a : ℚ) / b) H :=
  ⟨(rational_fraction_entries_le a b hb).1.trans haH,
    (rational_fraction_entries_le a b hb).2.trans hbH⟩

section Array

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def arrayDenominator (q : ι → ℚ) : ℕ := ∏ i, (q i).den

def clearedArray (q : ι → ℚ) (i : ι) : ℤ :=
  (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)

omit [DecidableEq ι] in
theorem arrayDenominator_pos (q : ι → ℚ) : 0 < arrayDenominator q :=
  Finset.prod_pos fun i _ => (q i).den_pos

omit [DecidableEq ι] in
theorem arrayDenominator_le (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, (q i).den ≤ H) :
    arrayDenominator q ≤ H ^ Fintype.card ι := by
  exact (Finset.prod_le_prod' fun i _ => hq i).trans_eq (by simp)

theorem arrayDenominator_eq (q : ι → ℚ) (i : ι) :
    arrayDenominator q = (q i).den * ∏ j ∈ Finset.univ.erase i, (q j).den := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem clearedArray_cast (q : ι → ℚ) (i : ι) :
    (clearedArray q i : ℚ) = (arrayDenominator q : ℚ) * q i := by
  rw [arrayDenominator_eq q i]
  have hq := Rat.num_div_den (q i)
  have hd : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  dsimp only [clearedArray]
  push_cast
  conv_rhs => rhs; rw [← hq]
  field_simp

theorem clearedArray_natAbs_le (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, RationalHeightLE (q i) H) (i : ι) :
    (clearedArray q i).natAbs ≤ H ^ Fintype.card ι := by
  have hprod : (∏ j ∈ Finset.univ.erase i, (q j).den) ≤
      H ^ (Finset.univ.erase i).card := by
    exact (Finset.prod_le_prod' fun j _ => (hq j).2).trans_eq (by simp)
  have hcard : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ i)
  calc
    (clearedArray q i).natAbs =
        (q i).num.natAbs * ∏ j ∈ Finset.univ.erase i, (q j).den := by
      simp only [clearedArray, Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ H * H ^ (Finset.univ.erase i).card := Nat.mul_le_mul (hq i).1 hprod
    _ = H ^ Fintype.card ι := by rw [← hcard, pow_succ, mul_comm]

theorem exists_bounded_integer_array (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, RationalHeightLE (q i) H) :
    ∃ D : ℕ, 0 < D ∧ D ≤ H ^ Fintype.card ι ∧
      ∃ a : ι → ℤ, (∀ i, (a i : ℚ) = (D : ℚ) * q i) ∧
        ∀ i, (a i).natAbs ≤ H ^ Fintype.card ι :=
  ⟨arrayDenominator q, arrayDenominator_pos q,
    arrayDenominator_le q (fun i => (hq i).2), clearedArray q,
    clearedArray_cast q, clearedArray_natAbs_le q hq⟩

end Array

end Erdos3

end

end OAI
