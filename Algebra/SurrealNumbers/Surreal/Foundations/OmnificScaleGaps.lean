import Surreal.Foundations.OmnificSupportBounds
import Surreal.Foundations.SignSequenceOrdinals

/-!
# Surreal scale gaps below small families

The actual-surreal assertions of `osq:lem:gap` and the ordinal family
`osq:eq:scales`. All family smallness is relative to the birthday universe.
Every small positive family has a positive scale whose every ordinary
multiple lies below the family. The interval below that scale is not small;
the explicit ordinal-indexed scales h/omega^(alpha+1) are distinct and
smaller than h by every ordinary factor.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Every small actual surreal family has simultaneous strict lower and upper bounds. -/
theorem small_two_sided_bounds {ι : Type v} [Small.{u} ι] (s : ι → SignSequence.{u}) :
    ∃ a b : SignSequence.{u}, ∀ i, a < s i ∧ s i < b := by
  obtain ⟨b, hb⟩ := small_upper_exponent_bound s
  obtain ⟨a, ha⟩ := small_upper_exponent_bound (fun i => -s i)
  exact ⟨-a, b, fun i => ⟨neg_lt.mp (ha i), hb i⟩⟩

/-- One positive scale is below every positive member of a small family by every ordinary factor. -/
theorem small_subordinate_scale {ι : Type v} [Small.{u} ι]
    (s : ι → SignSequence.{u}) (hs : ∀ i, 0 < s i) :
    ∃ h : SignSequence.{u}, 0 < h ∧ ∀ i (n : ℕ), (n : SignSequence) * h < s i := by
  let f : ι × ℕ → SignSequence.{u} := fun p => s p.1 / (p.2 + 1 : ℕ)
  have hf (p : ι × ℕ) : 0 < f p :=
    div_pos (hs p.1) (Nat.cast_pos.mpr (Nat.succ_pos _))
  obtain ⟨h, hh, hb⟩ := small_positive_exponent_bound f hf
  refine ⟨h, hh, fun i n => ?_⟩
  cases n with
  | zero => simpa only [Nat.cast_zero, zero_mul] using hs i
  | succ n =>
    have hd : (0 : SignSequence.{u}) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have he := (lt_div_iff₀ hd).mp (hb (i, n))
    simpa only [_root_.mul_comm] using he

/-- Every positive actual surreal interval is larger than the birthday universe. -/
theorem positive_interval_not_small (h : SignSequence.{u}) (hh : 0 < h) :
    ¬ Small.{u} (Set.Ioo 0 h) := by
  intro hsmall
  obtain ⟨a, ha, hb⟩ := small_positive_exponent_bound
    (fun x : Set.Ioo (0 : SignSequence.{u}) h => x.val) (fun x => x.property.1)
  have hhalf : h / 2 ∈ Set.Ioo (0 : SignSequence.{u}) h := ⟨by positivity, by linarith⟩
  have hah := hb ⟨h / 2, hhalf⟩
  have hahalf : a / 2 ∈ Set.Ioo (0 : SignSequence.{u}) h := ⟨by positivity, by linarith⟩
  have hbad := hb ⟨a / 2, hahalf⟩
  linarith

/-- The whole positive interval under a subordinate bound remains subordinate to the family. -/
theorem interval_subordinate {ι : Type v} (s : ι → SignSequence.{u}) (h : SignSequence.{u})
    (hb : ∀ i (n : ℕ), (n : SignSequence) * h < s i)
    (x : SignSequence.{u}) (hx : x ∈ Set.Ioo 0 h) (i : ι) (n : ℕ) :
    (n : SignSequence) * x < s i :=
  (mul_le_mul_of_nonneg_left hx.2.le (Nat.cast_nonneg n)).trans_lt (hb i n)

/-- The explicit ordinal-indexed scales printed in the manuscript. -/
def ordinalScale (h : SignSequence.{u}) (a : Ordinal.{u}) : SignSequence.{u} :=
  h / omegaPower (ofOrdinal a + 1)

/-- The field-sum exponent in the definition is literally the embedded ordinal successor. -/
theorem ordinalScale_eq (h : SignSequence.{u}) (a : Ordinal.{u}) :
    ordinalScale h a = h / omegaPower (ofOrdinal (a + 1)) := by
  rw [ordinalScale, ofOrdinal_add_one]

/-- Every scale in the ordinal family is positive. -/
theorem ordinalScale_pos (h : SignSequence.{u}) (hh : 0 < h) (a : Ordinal.{u}) :
    0 < ordinalScale h a := div_pos hh (omegaPower_pos _)

/-- Increasing the ordinal strictly decreases its positive scale. -/
theorem ordinalScale_strictAnti (h : SignSequence.{u}) (hh : 0 < h) : StrictAnti (ordinalScale h) := by
  intro a b hab
  apply div_lt_div_of_pos_left hh (omegaPower_pos _)
  apply omegaPower_strictMono
  have := ofOrdinal_strictMono hab
  linarith

/-- In particular every ordinal-indexed family has pairwise distinct scales. -/
theorem ordinalScale_injective (h : SignSequence.{u}) (hh : 0 < h) :
    Function.Injective (ordinalScale h) := (ordinalScale_strictAnti h hh).injective

/-- Every ordinary multiple of an ordinal scale is below its original scale. -/
theorem nat_mul_ordinalScale_lt (h : SignSequence.{u}) (hh : 0 < h) (a : Ordinal.{u}) (n : ℕ) :
    (n : SignSequence) * ordinalScale h a < h := by
  have hn : (n : SignSequence.{u}) < omegaPower 1 := by
    apply (le_abs_self _).trans_lt
    apply abs_lt_omegaPower_one_of_finite
    simpa only [map_natCast] using finite_ofReal (n : ℝ)
  have ha : (0 : SignSequence.{u}) ≤ ofOrdinal a := by
    simpa only [ofOrdinal_zero] using ofOrdinal_strictMono.monotone (show (0 : Ordinal.{u}) ≤ a from bot_le)
  have he : (n : SignSequence.{u}) < omegaPower (ofOrdinal a + 1) :=
    hn.trans_le (omegaPower_strictMono.monotone (by linarith))
  rw [ordinalScale, ← mul_div_assoc, div_lt_iff₀ (omegaPower_pos _)]
  simpa only [_root_.mul_comm] using mul_lt_mul_of_pos_right he hh

/-- The explicit ordinal scales are subordinate to every member of the original small family. -/
theorem ordinalScale_subordinate {ι : Type v} (s : ι → SignSequence.{u}) (h : SignSequence.{u})
    (hh : 0 < h) (hb : ∀ i (n : ℕ), (n : SignSequence) * h < s i)
    (a : Ordinal.{u}) (i : ι) (n : ℕ) : (n : SignSequence) * ordinalScale h a < s i := by
  have hi : h < s i := by simpa only [Nat.cast_one, _root_.one_mul] using hb i 1
  exact (nat_mul_ordinalScale_lt h hh a n).trans hi

end
end Surreal.Foundations.SignSequence
