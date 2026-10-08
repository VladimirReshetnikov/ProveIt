import GowersSzemeredi.Proofs16PolynomialRecurrenceProfile
import Mathlib.Analysis.SpecificLimits.Normed

/-! A strict eventual improvement of the Section 16 recurrence bound.

For fixed dimension and constants, polynomial growth is eventually below
the old geometric family-size loss. Thus the reciprocal-polynomial width
exponent is strictly larger, and its integer threshold is eventually no
larger than the old rounding-safe threshold. Combining this comparison
with the proved recurrence gives a stronger conclusion under the old
hypotheses for all sufficiently large phase families.

The crossover family size and the dimension constants are existential.
The result concerns the recurrence bound; it does not settle the remaining
structural theorems or compare the final all-length Szemeredi threshold.
-/
set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

theorem eventually_nat_polynomial_lt_geometric (A d b : Nat) (hb : 2 ≤ b) :
    ∀ᶠ q : Nat in atTop, A * (q + 1) ^ d < b ^ q := by
  by_cases hA : A = 0
  · filter_upwards [] with q
    simp only [hA, zero_mul]
    positivity
  have hAR : (0 : Real) < A := by exact_mod_cast (Nat.pos_of_ne_zero hA)
  have hbR : (1 : Real) < b := by exact_mod_cast (show 1 < b by omega)
  have heps : (0 : Real) < 1 / ((A : Real) * b) := by positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt d hbR
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds heps))
  filter_upwards [eventually_ge_atTop n] with q hq
  have h := hn (q + 1) (by omega)
  have hpow : (0 : Real) < (b : Real) ^ (q + 1) := by positivity
  have h' := (div_lt_iff₀ hpow).mp h
  have hprod : (A : Real) * ((q + 1 : Nat) : Real) ^ d < (b : Real) ^ q := by
    calc
      _ < (A : Real) * ((1 / ((A : Real) * b)) * (b : Real) ^ (q + 1)) :=
        mul_lt_mul_of_pos_left h' hAR
      _ = _ := by rw [pow_succ]; field_simp
  exact_mod_cast hprod

theorem section16_geometric_base_two_le (k : Nat) :
    2 ≤ section16K k ^ (2 ^ (k + 1)) := by
  have hK : 2 ≤ section16K k := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (k + 1) ^ 2 * 2 ^ (k + 4) := Nat.le_mul_of_pos_left _ (by positivity)
  apply hK.trans
  simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < section16K k)
    (Nat.one_le_two_pow : 1 ≤ 2 ^ (k + 1))

/-- For every fixed dimension and positive exponent constant, the new
recurrence exponent eventually exceeds the old exponential-in-q exponent. -/
theorem eventually_section16RecurrenceExponent_lt_simultaneous (k p : Nat) (hp : 0 < p) :
    ∀ᶠ q : Nat in atTop,
      section16RecurrenceExponent k q < section16SimultaneousExponent k p q := by
  have h := eventually_nat_polynomial_lt_geometric (2 * p) (2 * (2 ^ (k + 1)))
    (section16K k ^ (2 ^ (k + 1))) (section16_geometric_base_two_le k)
  filter_upwards [h] with q hq
  have hden : ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))) : Real) <
      (section16K k : Real) ^ (2 ^ (k + 1) * q) := by
    have hh : 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) <
        section16K k ^ (2 ^ (k + 1) * q) := by simpa only [pow_mul, Nat.mul_assoc] using hq
    exact_mod_cast hh
  have hpos : (0 : Real) < 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) := by positivity
  have hinv := inv_strictAnti₀ hpos hden
  unfold section16RecurrenceExponent
  rw [zpow_neg, zpow_natCast]
  simpa only [section16SimultaneousExponent, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hinv

/-- The new integer threshold is eventually no larger than the existing
rounding-safe threshold, for any fixed choice of dimension constants. -/
theorem eventually_section16SimultaneousThreshold_le_old (k K p : Nat) :
    ∀ᶠ q : Nat in atTop, section16SimultaneousThreshold k K p q ≤ section16WidthThreshold k q := by
  have h := eventually_nat_polynomial_lt_geometric (2 * p * K) (2 * (2 ^ (k + 1)) + 1)
    (section16K k ^ (2 ^ (k + 1))) (section16_geometric_base_two_le k)
  filter_upwards [h] with q hq
  have hbase : K * (q + 1) ≤ 2 ^ (K * (q + 1)) := Nat.lt_two_pow_self.le
  have hexp : K * (q + 1) * (2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))) ≤
      section16K k ^ (2 ^ (k + 1) * q) := by
    have heq : K * (q + 1) * (2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))) =
        (2 * p * K) * (q + 1) ^ (2 * (2 ^ (k + 1)) + 1) := by rw [pow_succ]; ring
    rw [heq, pow_mul]
    exact hq.le
  have hT : 1 ≤ polynomialPartitionThreshold (k + 1) := by
    unfold polynomialPartitionThreshold weylThreshold
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc
    section16SimultaneousThreshold k K p q ≤
        (2 ^ (K * (q + 1))) ^ (2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))) := Nat.pow_le_pow_left hbase _
    _ = 2 ^ (K * (q + 1) * (2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))))) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (section16K k ^ (2 ^ (k + 1) * q)) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ section16WidthThreshold k q := Nat.pow_le_pow_left (by omega) _

/-- For every dimension, all sufficiently large phase families admit a
strictly better recurrence exponent under the old width threshold. -/
theorem exists_eventually_stronger_section16_recurrence (k : Nat) :
    ∃ K p q0 : Nat, 2 ≤ K ∧ 0 < p ∧ ∀ q : Nat, q0 ≤ q →
      section16RecurrenceExponent k q < section16SimultaneousExponent k p q ∧
      ∀ (N m : Nat) [NeZero N] (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        section16WidthThreshold k q ≤ m → m ≤ P.width →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (∀ j, (m : Real) ^ section16SimultaneousExponent k p q ≤ (Q j).width) ∧
          ∀ i j x, x ∈ (Q j).carrier →
            (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
              2 * (m : Real) ^ (-section16SimultaneousExponent k p q) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_polynomial_section16_recurrence_profile k
  obtain ⟨q0, hq0⟩ := eventually_atTop.mp
    ((eventually_section16RecurrenceExponent_lt_simultaneous k p hp).and
      (eventually_section16SimultaneousThreshold_le_old k K p))
  refine ⟨K, p, q0, hK, hp, fun q hq => ⟨(hq0 q hq).1, ?_⟩⟩
  intro N m _ P hP mu hmu hm hmP
  exact hpartition N q m P hP mu hmu ((hq0 q hq).2.trans hm) hmP

end LeanProofs.GowersSzemeredi
