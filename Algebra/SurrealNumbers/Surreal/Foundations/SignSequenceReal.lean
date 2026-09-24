import Surreal.Foundations.SignSequenceRationals
import CombinatorialGames.Surreal.Real

/-!
# Ordinary real numbers in the constructed sign field

The upstream Dedekind-cut embedding of ordinary `ℝ` into numeric games
composes with the proved sign/game field equivalence. This supplies the real
coefficient embedding required by `found:eq:normalform` and
`found:sub:hahnworkspace`, without proving the Hahn normal-form bridge.
The embedding preserves and reflects order
and agrees with the existing rational, integer and natural-number casts.
The concrete scale `ω` is above every embedded real, and its reciprocal is
positive and below every positive embedded real, as required to distinguish
ordinary real scales from surreal scales in `found:sub:modulus`.

This module proves no birthday bound for arbitrary real numbers and no
real-closedness or Hahn normal-form theorem for the sign field.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The ordered field embedding of ordinary real numbers into the concrete
sign carrier, using the upstream dyadic Dedekind-cut construction. -/
def ofReal : ℝ →+*o SignSequence.{u} where
  toRingHom := toSurrealRingEquiv.symm.toRingHom.comp _root_.Real.toSurrealRingHom.toRingHom
  monotone' := toSurrealOrderIso.symm.monotone.comp _root_.Real.toSurrealEmbedding.monotone

/-- The real embedding agrees with the upstream numeric-game construction. -/
@[simp] theorem toSurreal_ofReal (r : ℝ) :
    toSurreal (ofReal r : SignSequence.{u}) = _root_.Real.toSurreal r :=
  toSurreal_orderIso_symm _

@[simp] theorem ofReal_le_iff (r s : ℝ) :
    (ofReal r : SignSequence.{u}) ≤ ofReal s ↔ r ≤ s := by
  rw [← toSurreal_le_iff, toSurreal_ofReal, toSurreal_ofReal]
  exact _root_.Real.toSurreal_le_iff

@[simp] theorem ofReal_lt_iff (r s : ℝ) :
    (ofReal r : SignSequence.{u}) < ofReal s ↔ r < s := by
  rw [← toSurreal_lt_iff, toSurreal_ofReal, toSurreal_ofReal]
  exact _root_.Real.toSurreal_lt_iff

theorem ofReal_strictMono : StrictMono (ofReal : ℝ → SignSequence.{u}) :=
  fun _ _ h => (ofReal_lt_iff _ _).mpr h

theorem ofReal_injective : Function.Injective (ofReal : ℝ → SignSequence.{u}) :=
  ofReal_strictMono.injective

@[simp] theorem ofReal_inj (r s : ℝ) :
    (ofReal r : SignSequence.{u}) = ofReal s ↔ r = s := ofReal_injective.eq_iff

/-- The same real inclusion bundled as an order embedding. -/
def realOrderEmbedding : ℝ ↪o SignSequence.{u} :=
  OrderEmbedding.ofStrictMono ofReal ofReal_strictMono

@[simp] theorem realOrderEmbedding_apply (r : ℝ) :
    realOrderEmbedding r = (ofReal r : SignSequence.{u}) := rfl

@[simp] theorem ofReal_zero : (ofReal 0 : SignSequence.{u}) = 0 := map_zero ofReal
@[simp] theorem ofReal_one : (ofReal 1 : SignSequence.{u}) = 1 := map_one ofReal

@[simp] theorem ofReal_add (r s : ℝ) :
    (ofReal (r + s) : SignSequence.{u}) = ofReal r + ofReal s := map_add ofReal r s

@[simp] theorem ofReal_mul (r s : ℝ) :
    (ofReal (r * s) : SignSequence.{u}) = ofReal r * ofReal s := map_mul ofReal r s

@[simp] theorem ofReal_neg (r : ℝ) :
    (ofReal (-r) : SignSequence.{u}) = -ofReal r := map_neg ofReal r

@[simp] theorem ofReal_sub (r s : ℝ) :
    (ofReal (r - s) : SignSequence.{u}) = ofReal r - ofReal s := map_sub ofReal r s

@[simp] theorem ofReal_inv (r : ℝ) :
    (ofReal r⁻¹ : SignSequence.{u}) = (ofReal r)⁻¹ := map_inv₀ ofReal r

@[simp] theorem ofReal_div (r s : ℝ) :
    (ofReal (r / s) : SignSequence.{u}) = ofReal r / ofReal s := map_div₀ ofReal r s

/-- The real embedding extends the native natural-number cast. -/
@[simp] theorem ofReal_natCast (n : ℕ) : (ofReal n : SignSequence.{u}) = n := map_natCast ofReal n

/-- The real embedding extends the native integer cast. -/
@[simp] theorem ofReal_intCast (n : ℤ) : (ofReal n : SignSequence.{u}) = n := map_intCast ofReal n

/-- The real embedding extends the native rational field embedding. -/
@[simp] theorem ofReal_ratCast (q : ℚ) : (ofReal q : SignSequence.{u}) = q := map_ratCast ofReal q

/-- In particular, the dyadic rationals in the ordinary reals map to the
same dyadic values in the sign field. This makes no birthday assertion. -/
@[simp] theorem ofReal_dyadic (q : Dyadic) :
    (ofReal (q.toRat : ℝ) : SignSequence.{u}) = (q.toRat : SignSequence.{u}) := ofReal_ratCast _

/-- The all-plus sequence of length `ω` is larger than every ordinary real
in the concrete real embedding. -/
theorem ofReal_lt_omega0 (r : ℝ) :
    (ofReal r : SignSequence.{u}) < ofOrdinal Ordinal.omega0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have h : (ofReal r : SignSequence.{u}) < n := by
    simpa only [ofReal_natCast] using (ofReal_lt_iff r n).mpr hn
  exact h.trans (natCast_lt_omega0 n)

/-- The concrete infinite scale is outside the ordinary real subfield. -/
theorem omega0_not_mem_range_ofReal :
    (ofOrdinal Ordinal.omega0 : SignSequence.{u}) ∉ Set.range ofReal := by
  rintro ⟨r, hr⟩
  exact (ofReal_lt_omega0 r).ne hr

/-- The reciprocal of `ω` is smaller than every positive ordinary real.
This is an actual field element, with the scale distinction used in
`found:sub:modulus`; it is not an assertion about a real-valued norm. -/
theorem inv_omega0_lt_ofReal (r : ℝ) (hr : 0 < r) :
    (ofOrdinal Ordinal.omega0 : SignSequence.{u})⁻¹ < ofReal r := by
  have hr' : (0 : SignSequence.{u}) < ofReal r := by
    simpa only [ofReal_zero] using (ofReal_lt_iff 0 r).mpr hr
  have hinv : (0 : SignSequence.{u}) < (ofReal r)⁻¹ := inv_pos.mpr hr'
  have hlt : (ofReal r : SignSequence.{u})⁻¹ < ofOrdinal Ordinal.omega0 := by
    simpa only [ofReal_inv] using ofReal_lt_omega0.{u} r⁻¹
  simpa only [inv_inv] using (inv_lt_inv₀ omega0_pos hinv).mpr hlt

/-- A positive infinitesimal measured against all positive ordinary reals,
witnessed by the reciprocal of the all-plus sequence of length `ω`. -/
theorem exists_pos_lt_all_pos_ofReal :
    ∃ ε : SignSequence.{u}, 0 < ε ∧ ∀ r : ℝ, 0 < r → ε < ofReal r :=
  ⟨(ofOrdinal Ordinal.omega0)⁻¹, inv_omega0_pos, inv_omega0_lt_ofReal⟩

end

end Surreal.Foundations.SignSequence
