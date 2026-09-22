import Surreal.Foundations.SignSequenceField
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Rational numbers and infinite scales in the sign field

Native rational casts give compatible ring and order embeddings into the
constructed sign field. The all-plus sequence of length `ω` dominates every
rational cast, refuting the native `Archimedean` property. Its reciprocal is
positive and smaller than every positive rational cast.

The halving results prove the remaining upper-bound argument in
`found:prop:incomplete`: if `h` bounds the natural numbers then `h / 2` is a
strictly smaller upper bound, and every natural number is strictly below it.
These are consequences of the constructed ordered field; no real-closedness,
dyadic birthday classification, or Hahn-series identification is assumed.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The native rational embedding as a ring homomorphism. -/
def rationalRingHom : ℚ →+* SignSequence.{u} := Rat.castHom _

@[simp] theorem rationalRingHom_apply (q : ℚ) :
    rationalRingHom q = (q : SignSequence.{u}) := rfl

/-- Rational casts preserve and reflect strict order. -/
theorem ratCast_strictMono : StrictMono (Rat.cast : ℚ → SignSequence.{u}) :=
  Rat.cast_strictMono

theorem rationalRingHom_injective :
    Function.Injective (rationalRingHom : ℚ → SignSequence.{u}) :=
  ratCast_strictMono.injective

/-- The same native rational embedding, bundled with its order preservation. -/
def rationalOrderEmbedding : ℚ ↪o SignSequence.{u} := Rat.castOrderEmbedding

@[simp] theorem rationalOrderEmbedding_apply (q : ℚ) :
    rationalOrderEmbedding q = (q : SignSequence.{u}) := rfl

theorem ratCast_lt_iff (p q : ℚ) :
    (p : SignSequence.{u}) < q ↔ p < q := Rat.cast_lt

theorem ratCast_pos_iff (q : ℚ) :
    (0 : SignSequence.{u}) < q ↔ 0 < q := Rat.cast_pos

/-- Rational numbers agree under the sign/game field identification. -/
@[simp] theorem toSurreal_ratCast (q : ℚ) :
    toSurreal (q : SignSequence.{u}) = (q : _root_.Surreal.{u}) :=
  map_ratCast toSurrealRingEquiv q

/-- The infinite all-plus ordinal is positive. -/
theorem omega0_pos : (0 : SignSequence.{u}) < ofOrdinal Ordinal.omega0 := by
  simpa only [Nat.cast_zero] using natCast_lt_omega0.{u} 0

/-- Every rational number is smaller than the same concrete infinite ordinal. -/
theorem ratCast_lt_omega0 (q : ℚ) :
    (q : SignSequence.{u}) < ofOrdinal Ordinal.omega0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  exact (Rat.cast_lt_natCast.mpr hn).trans (natCast_lt_omega0 n)

/-- The native ordered additive group of sign sequences is not Archimedean. -/
theorem not_archimedean : ¬ Archimedean SignSequence.{u} := by
  intro h
  letI := h
  obtain ⟨n, hn⟩ := exists_nat_gt (ofOrdinal Ordinal.omega0 : SignSequence.{u})
  exact (natCast_lt_omega0 n).not_gt hn

/-- The strict inequality in the halving proof of `found:prop:incomplete`.
The upper-bound hypothesis at `2 * n + 1` makes the result strict. -/
theorem natCast_lt_half_of_mem_upperBounds {h : SignSequence.{u}}
    (hh : h ∈ upperBounds (Set.range (Nat.cast : ℕ → SignSequence.{u})))
    (n : ℕ) : (n : SignSequence.{u}) < h / 2 := by
  have hb := hh (Set.mem_range_self (2 * n + 1))
  have hb' : 2 * (n : SignSequence.{u}) + 1 ≤ h := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb
  apply (lt_div_iff₀ (by positivity : (0 : SignSequence.{u}) < 2)).mpr
  linarith

/-- Every upper bound of the natural numbers can be halved to give a strictly
smaller upper bound, as in `found:prop:incomplete`. -/
theorem half_mem_upperBounds_natCast {h : SignSequence.{u}}
    (hh : h ∈ upperBounds (Set.range (Nat.cast : ℕ → SignSequence.{u}))) :
    h / 2 ∈ upperBounds (Set.range (Nat.cast : ℕ → SignSequence.{u})) ∧ h / 2 < h := by
  constructor
  · rintro x ⟨n, rfl⟩
    exact (natCast_lt_half_of_mem_upperBounds hh n).le
  · apply half_lt_self
    have hb := hh (Set.mem_range_self 1)
    exact zero_lt_one.trans_le (by simpa only [Nat.cast_one] using hb)

/-- The halving argument alone rules out a least upper bound of the native
natural-number range. -/
theorem natCast_range_no_isLUB_by_halving :
    ¬ ∃ h : SignSequence.{u}, IsLUB (Set.range (Nat.cast : ℕ → SignSequence.{u})) h := by
  rintro ⟨h, hh⟩
  obtain ⟨hbound, hlt⟩ := half_mem_upperBounds_natCast hh.1
  exact hlt.not_ge (hh.2 hbound)

/-- The reciprocal of the infinite ordinal is a concrete positive element. -/
theorem inv_omega0_pos : (0 : SignSequence.{u}) < (ofOrdinal Ordinal.omega0)⁻¹ :=
  inv_pos.mpr omega0_pos

/-- The concrete reciprocal is smaller than `1 / n` for every positive natural
number; the positivity guard excludes the total inverse at zero. -/
theorem inv_omega0_lt_one_div_natCast (n : ℕ) (hn : 0 < n) :
    (ofOrdinal Ordinal.omega0 : SignSequence.{u})⁻¹ < 1 / (n : SignSequence.{u}) := by
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (Nat.cast_pos.mpr hn) (natCast_lt_omega0 n)

/-- In fact, the reciprocal is smaller than every positive rational cast. -/
theorem inv_omega0_lt_ratCast (q : ℚ) (hq : 0 < q) :
    (ofOrdinal Ordinal.omega0 : SignSequence.{u})⁻¹ < q := by
  have hinv : (0 : SignSequence.{u}) < (q : SignSequence.{u})⁻¹ :=
    inv_pos.mpr (Rat.cast_pos.mpr hq)
  have hlt : (q : SignSequence.{u})⁻¹ < ofOrdinal Ordinal.omega0 := by
    simpa only [Rat.cast_inv] using ratCast_lt_omega0.{u} q⁻¹
  simpa only [inv_inv] using (inv_lt_inv₀ omega0_pos hinv).mpr hlt

/-- A positive infinitesimal exists in the concrete field, with its size
measured against all positive rational numbers. -/
theorem exists_pos_lt_all_pos_ratCast :
    ∃ ε : SignSequence.{u}, 0 < ε ∧ ∀ q : ℚ, 0 < q → ε < q :=
  ⟨(ofOrdinal Ordinal.omega0)⁻¹, inv_omega0_pos, inv_omega0_lt_ratCast⟩

end

end Surreal.Foundations.SignSequence
