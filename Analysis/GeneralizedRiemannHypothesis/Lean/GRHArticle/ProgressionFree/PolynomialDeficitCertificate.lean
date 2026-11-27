import GRHArticle.ProgressionFree.Rankin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# A finite certificate for the polynomial deficit replacement

The list of deficits is the translated slice from the archived scripts
`grh-methods-polynomial-density/check_tilted.py` and
`grh_beyond_dirichlet_2026-11-25/code/check_density_certificate.py` at
`10802a6b36`. These are the finite inputs of `gpp:thm:counterexample`.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

private def polynomialDeficitList : List ℕ :=
  [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53, 57, 67,
   111, 112, 115, 116, 122, 124, 125, 127, 131, 141, 148, 149, 152, 153,
   159, 161, 162, 164, 168, 178, 333, 334, 337, 338, 344, 346, 347, 349,
   353, 363, 370, 371, 374, 375, 381, 383, 384, 386, 390, 437, 440, 441,
   444, 449, 450, 453, 455, 464, 467, 468, 471, 476, 477, 480]

/-- The 74 deficits of the weighted replacement rule. -/
def polynomialDeficitWitness : Finset ℕ := polynomialDeficitList.toFinset

theorem polynomialDeficitWitness_card : polynomialDeficitWitness.card = 74 := by decide

theorem polynomialDeficitWitness_max_le : ∀ d ∈ polynomialDeficitWitness, d ≤ 480 := by decide

private def midpointCheck (D : List ℕ) : Bool :=
  D.all fun a ↦ D.all fun c ↦
    if a < c ∧ (a + c) % 2 = 0 then !(D.contains ((a + c) / 2)) else true

set_option maxHeartbeats 5000000 in
private theorem midpointCheck_witness : midpointCheck polynomialDeficitList = true := by decide

/-- The translated deficit list has no nonconstant three-term arithmetic progression. -/
theorem threeAPFree_polynomialDeficitWitness :
    ThreeAPFree (polynomialDeficitWitness : Set ℕ) := by
  have hcheck := List.all_eq_true.mp midpointCheck_witness
  have hblocked {a b c : ℕ} (ha : a ∈ polynomialDeficitList) (hb : b ∈ polynomialDeficitList)
      (hc : c ∈ polynomialDeficitList) (hac : a < c) (h : a + c = b + b) : False := by
    have hc' := List.all_eq_true.mp (hcheck a ha) c hc
    have hcond : a < c ∧ (a + c) % 2 = 0 := ⟨hac, by omega⟩
    have hmid : (a + c) / 2 = b := by omega
    simp [if_pos hcond, hmid] at hc'
    exact hc' hb
  intro a ha b hb c hc h
  have ha' : a ∈ polynomialDeficitList := List.mem_toFinset.mp ha
  have hb' : b ∈ polynomialDeficitList := List.mem_toFinset.mp hb
  have hc' : c ∈ polynomialDeficitList := List.mem_toFinset.mp hc
  have heq : a = c := le_antisymm
    (le_of_not_gt fun hca ↦ hblocked hc' hb' ha' hca (by omega))
    (le_of_not_gt fun hac ↦ hblocked ha' hb' hc' hac h)
  omega

/-- The 128 binary-ternary digit vectors of length at most seven, read as integers. -/
def ternaryDeficitPrefix : Finset ℕ :=
  (Finset.range 2187).filter fun n ↦ (Nat.digits 3 n).all (fun d ↦ decide (d ≤ 1))

theorem mem_ternaryDeficitPrefix (n : ℕ) :
    n ∈ ternaryDeficitPrefix ↔ n < 2187 ∧ n ∈ greedyExponents := by
  simp [ternaryDeficitPrefix, greedyExponents, List.all_eq_true]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem ternaryDeficitPrefix_card : ternaryDeficitPrefix.card = 128 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem ternaryDeficitPrefix_max_le : ∀ d ∈ ternaryDeficitPrefix, d ≤ 1093 := by decide

private def scaledDeficitWeight (D : Finset ℕ) : ℕ :=
  ∑ d ∈ D, 127 ^ d * 128 ^ (1093 - d)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
set_option exponentiation.threshold 4096 in
private theorem scaledDeficitWeight_gain :
    1000 * scaledDeficitWeight ternaryDeficitPrefix + 16 * 128 ^ 1093 <
      1000 * scaledDeficitWeight polynomialDeficitWitness := by decide

private theorem cast_scaledDeficitWeight (D : Finset ℕ) (h : ∀ d ∈ D, d ≤ 1093) :
    (scaledDeficitWeight D : ℚ) = (128 : ℚ) ^ 1093 * ∑ d ∈ D, ((127 : ℚ) / 128) ^ d := by
  simp only [scaledDeficitWeight, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [div_pow, ← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero d (by norm_num : (128 : ℚ) ≠ 0))).2
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (h d hd), mul_comm]

/-- Clearing the common denominator proves a finite gain greater than (16/1000). -/
theorem polynomialDeficitWeight_gain :
    (16 : ℚ) / 1000 <
      (∑ d ∈ polynomialDeficitWitness, ((127 : ℚ) / 128) ^ d) -
        ∑ d ∈ ternaryDeficitPrefix, ((127 : ℚ) / 128) ^ d := by
  have h : (1000 : ℚ) * (scaledDeficitWeight ternaryDeficitPrefix : ℚ) +
      16 * (128 : ℚ) ^ 1093 < 1000 * (scaledDeficitWeight polynomialDeficitWitness : ℚ) := by
    exact_mod_cast scaledDeficitWeight_gain
  rw [cast_scaledDeficitWeight ternaryDeficitPrefix ternaryDeficitPrefix_max_le,
    cast_scaledDeficitWeight polynomialDeficitWitness (fun d hd ↦
      (polynomialDeficitWitness_max_le d hd).trans (by decide))] at h
  have hpos : 0 < (128 : ℚ) ^ 1093 := by positivity
  generalize (128 : ℚ) ^ 1093 = D at h hpos
  apply (mul_lt_mul_iff_right₀ hpos).mp
  nlinarith only [h]

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
private theorem polynomialDeficitTail_integer :
    128 * 127 ^ 2187 * 100000 < (128 : ℕ) ^ 2187 := by decide

/-- The full geometric tail starting at (3^7) is less than (1/100000). -/
theorem polynomialDeficitTail_bound :
    (128 : ℚ) * ((127 : ℚ) / 128) ^ 2187 < 1 / 100000 := by
  rw [div_pow, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num), one_mul]
  exact_mod_cast polynomialDeficitTail_integer

end GRHArticle.ProgressionFree
