import Surreal.Foundations.SignSequenceStandardPart
import CombinatorialGames.Surreal.Leading

/-!
# Conway monomials and leading data on the actual sign field

These are the monomial and leading-term prerequisites of `found:eq:normalform`
and `found:sub:hahnworkspace` in the foundations article. The proved sign/game
field equivalence transports the Conway omega-map and omega-logarithm from
the pinned upstream construction. The leading coefficient agrees with the
standard part of the normalized sign-field element.

The exponent here measures growth: `omegaPower a` increases with `a`.
The documents' Hahn convention is `t^a = omegaPower (-a)`. No expansion into
an infinite Hahn series or preservation of strong sums is asserted here.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The existing sign/game field equivalence also preserves the numerical order. -/
def toSurrealOrderRingIso : SignSequence.{u} ≃+*o _root_.Surreal.{u} where
  __ := toSurrealRingEquiv
  map_le_map_iff' := toSurreal_le_iff _ _

@[simp] theorem toSurrealOrderRingIso_apply (x : SignSequence.{u}) :
    toSurrealOrderRingIso x = toSurreal x := rfl

/-- Archimedean comparisons are preserved by the actual sign/game equivalence. -/
theorem archimedeanClass_toSurreal_le_iff (x y : SignSequence.{u}) :
    ArchimedeanClass.mk (toSurreal x) ≤ ArchimedeanClass.mk (toSurreal y) ↔
      ArchimedeanClass.mk x ≤ ArchimedeanClass.mk y := by
  constructor
  · intro h
    have h' := ArchimedeanClass.map_mk_le
      toSurrealOrderRingIso.symm.toOrderRingHom.toOrderAddMonoidHom h
    change ArchimedeanClass.mk (toSurrealOrderRingIso.symm (toSurrealOrderRingIso x)) ≤
      ArchimedeanClass.mk (toSurrealOrderRingIso.symm (toSurrealOrderRingIso y)) at h'
    simpa only [OrderRingIso.symm_apply_apply] using h'
  · exact ArchimedeanClass.map_mk_le
      toSurrealOrderRingIso.toOrderRingHom.toOrderAddMonoidHom

theorem archimedeanClass_toSurreal_lt_iff (x y : SignSequence.{u}) :
    ArchimedeanClass.mk (toSurreal x) < ArchimedeanClass.mk (toSurreal y) ↔
      ArchimedeanClass.mk x < ArchimedeanClass.mk y := by
  rw [lt_iff_not_ge, archimedeanClass_toSurreal_le_iff, lt_iff_not_ge]

theorem archimedeanClass_toSurreal_eq_iff (x y : SignSequence.{u}) :
    ArchimedeanClass.mk (toSurreal x) = ArchimedeanClass.mk (toSurreal y) ↔
      ArchimedeanClass.mk x = ArchimedeanClass.mk y := by
  simp only [le_antisymm_iff, archimedeanClass_toSurreal_le_iff]

theorem archimedeanClass_toSurreal_eq_zero_iff (x : SignSequence.{u}) :
    ArchimedeanClass.mk (toSurreal x) = 0 ↔ ArchimedeanClass.mk x = 0 := by
  simpa only [toSurreal_one, ArchimedeanClass.mk_one] using
    archimedeanClass_toSurreal_eq_iff x 1

theorem finite_toSurreal_iff (x : SignSequence.{u}) :
    0 ≤ ArchimedeanClass.mk (toSurreal x) ↔ IsFinite x := by
  simpa only [toSurreal_one, ArchimedeanClass.mk_one, IsFinite] using
    archimedeanClass_toSurreal_le_iff 1 x

theorem infinitesimal_toSurreal_iff (x : SignSequence.{u}) :
    0 < ArchimedeanClass.mk (toSurreal x) ↔ IsInfinitesimal x := by
  simpa only [toSurreal_one, ArchimedeanClass.mk_one, IsInfinitesimal] using
    archimedeanClass_toSurreal_lt_iff 1 x

/-- Standard part commutes with the actual field equivalence on finite inputs. -/
theorem standardPart_toSurreal {x : SignSequence.{u}} (hx : IsFinite x) :
    ArchimedeanClass.stdPart (toSurreal x) = standardPart x := by
  have h := ArchimedeanClass.mk_sub_stdPart_pos _root_.Real.toSurrealRingHom
    ((finite_toSurreal_iff x).mpr hx)
  change 0 < ArchimedeanClass.mk (toSurreal x -
    _root_.Real.toSurreal (ArchimedeanClass.stdPart (toSurreal x))) at h
  have h' : IsInfinitesimal
      (x - ofReal (ArchimedeanClass.stdPart (toSurreal x))) := by
    apply (infinitesimal_toSurreal_iff _).mp
    simpa only [toSurreal_sub, toSurreal_ofReal] using h
  exact ((infinitesimal_sub_ofReal_iff hx).mp h').symm

/-- The Conway monomial `omega^x`, transported to the actual sign carrier. -/
def omegaPower (x : SignSequence.{u}) : SignSequence.{u} :=
  toSurrealOrderIso.symm (ω^ (toSurreal x))

@[simp] theorem toSurreal_omegaPower (x : SignSequence.{u}) :
    toSurreal (omegaPower x) = ω^ (toSurreal x) := toSurreal_orderIso_symm _

theorem omegaPower_pos (x : SignSequence.{u}) : 0 < omegaPower x := by
  apply (toSurreal_lt_iff _ _).mp
  simpa only [toSurreal_zero, toSurreal_omegaPower] using _root_.Surreal.wpow_pos (toSurreal x)

theorem omegaPower_ne_zero (x : SignSequence.{u}) : omegaPower x ≠ 0 :=
  (omegaPower_pos x).ne'

theorem omegaPower_strictMono : StrictMono (omegaPower : SignSequence.{u} → _) := by
  intro x y h
  apply (toSurreal_lt_iff _ _).mp
  simpa only [toSurreal_omegaPower] using
    _root_.Surreal.strictMono_wpow ((toSurreal_lt_iff _ _).mpr h)

@[simp] theorem omegaPower_lt_omegaPower (x y : SignSequence.{u}) :
    omegaPower x < omegaPower y ↔ x < y := omegaPower_strictMono.lt_iff_lt

@[simp] theorem omegaPower_le_omegaPower (x y : SignSequence.{u}) :
    omegaPower x ≤ omegaPower y ↔ x ≤ y := omegaPower_strictMono.le_iff_le

@[simp] theorem omegaPower_inj (x y : SignSequence.{u}) :
    omegaPower x = omegaPower y ↔ x = y := omegaPower_strictMono.injective.eq_iff

@[simp] theorem omegaPower_zero : omegaPower (0 : SignSequence.{u}) = 1 := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem omegaPower_add (x y : SignSequence.{u}) :
    omegaPower (x + y) = omegaPower x * omegaPower y := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem omegaPower_neg (x : SignSequence.{u}) :
    omegaPower (-x) = (omegaPower x)⁻¹ := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem omegaPower_sub (x y : SignSequence.{u}) :
    omegaPower (x - y) = omegaPower x / omegaPower y := by
  apply (toSurreal_inj _ _).mp
  simp

theorem omegaPower_nat_mul (n : ℕ) (x : SignSequence.{u}) :
    omegaPower (n * x) = omegaPower x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_one_mul, omegaPower_add, ih, pow_succ]

theorem omegaPower_mul_eq_iff (x y z : SignSequence.{u}) :
    omegaPower x * omegaPower y = omegaPower z ↔ x + y = z := by
  rw [← omegaPower_add, omegaPower_inj]

/-- The growth exponent of a nonzero sign-field element. Its total value at zero is zero. -/
def leadingExponent (x : SignSequence.{u}) : SignSequence.{u} :=
  toSurrealOrderIso.symm (_root_.Surreal.wlog (toSurreal x))

@[simp] theorem toSurreal_leadingExponent (x : SignSequence.{u}) :
    toSurreal (leadingExponent x) = _root_.Surreal.wlog (toSurreal x) :=
  toSurreal_orderIso_symm _

@[simp] theorem leadingExponent_zero : leadingExponent (0 : SignSequence.{u}) = 0 := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem leadingExponent_one : leadingExponent (1 : SignSequence.{u}) = 0 := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem leadingExponent_omegaPower (x : SignSequence.{u}) :
    leadingExponent (omegaPower x) = x := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem leadingExponent_ofReal (r : ℝ) :
    leadingExponent (ofReal r : SignSequence.{u}) = 0 := by
  apply (toSurreal_inj _ _).mp
  simp

@[simp] theorem leadingExponent_neg (x : SignSequence.{u}) :
    leadingExponent (-x) = leadingExponent x := by
  apply (toSurreal_inj _ _).mp
  simp

private theorem toSurreal_ne_zero {x : SignSequence.{u}} (hx : x ≠ 0) : toSurreal x ≠ 0 := by
  intro h
  exact hx ((toSurreal_inj x 0).mp (h.trans toSurreal_zero.symm))

@[simp] theorem leadingExponent_mul {x y : SignSequence.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    leadingExponent (x * y) = leadingExponent x + leadingExponent y := by
  apply (toSurreal_inj _ _).mp
  simpa only [toSurreal_mul, toSurreal_add, toSurreal_leadingExponent] using
    _root_.Surreal.wlog_mul (toSurreal_ne_zero hx)
      (toSurreal_ne_zero hy)

@[simp] theorem leadingExponent_inv (x : SignSequence.{u}) :
    leadingExponent x⁻¹ = -leadingExponent x := by
  apply (toSurreal_inj _ _).mp
  simp

theorem leadingExponent_div {x y : SignSequence.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    leadingExponent (x / y) = leadingExponent x - leadingExponent y := by
  simp only [div_eq_mul_inv, leadingExponent_mul hx (inv_ne_zero hy),
    leadingExponent_inv, sub_eq_add_neg]

@[simp] theorem leadingExponent_pow (x : SignSequence.{u}) (n : ℕ) :
    leadingExponent (x ^ n) = n * leadingExponent x := by
  apply (toSurreal_inj _ _).mp
  have hp : toSurreal (x ^ n) = toSurreal x ^ n := map_pow toSurrealRingEquiv x n
  have hn : toSurreal (n : SignSequence.{u}) = n := map_natCast toSurrealRingEquiv n
  simp only [toSurreal_leadingExponent, toSurreal_mul, hp, hn, _root_.Surreal.wlog_pow]

/-- Growth exponents reverse the order of native Archimedean valuation classes.
Both nonzero hypotheses are essential because the exponent at zero is a junk value. -/
theorem leadingExponent_le_iff {x y : SignSequence.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    leadingExponent x ≤ leadingExponent y ↔ ArchimedeanClass.mk y ≤ ArchimedeanClass.mk x := by
  rw [← toSurreal_le_iff, toSurreal_leadingExponent, toSurreal_leadingExponent,
    _root_.Surreal.wlog_le_wlog_iff (toSurreal_ne_zero hx)
      (toSurreal_ne_zero hy), _root_.Surreal.vle_def,
    archimedeanClass_toSurreal_le_iff]

theorem leadingExponent_lt_iff {x y : SignSequence.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    leadingExponent x < leadingExponent y ↔ ArchimedeanClass.mk y < ArchimedeanClass.mk x := by
  rw [lt_iff_not_ge, leadingExponent_le_iff hy hx, lt_iff_not_ge]

theorem leadingExponent_eq_iff {x y : SignSequence.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    leadingExponent x = leadingExponent y ↔ ArchimedeanClass.mk x = ArchimedeanClass.mk y := by
  simp only [le_antisymm_iff, leadingExponent_le_iff hx hy, leadingExponent_le_iff hy hx,
    and_comm]

/-- The growth exponent is nonpositive exactly on nonzero finite elements. -/
theorem finite_iff_leadingExponent_nonpos {x : SignSequence.{u}} (hx : x ≠ 0) :
    IsFinite x ↔ leadingExponent x ≤ 0 := by
  simpa only [leadingExponent_one, ArchimedeanClass.mk_one, IsFinite] using
    (leadingExponent_le_iff hx one_ne_zero).symm

theorem infinitesimal_iff_leadingExponent_neg {x : SignSequence.{u}} (hx : x ≠ 0) :
    IsInfinitesimal x ↔ leadingExponent x < 0 := by
  simpa only [leadingExponent_one, ArchimedeanClass.mk_one, IsInfinitesimal] using
    (leadingExponent_lt_iff hx one_ne_zero).symm

theorem leadingExponent_eq_zero_iff {x : SignSequence.{u}} (hx : x ≠ 0) :
    leadingExponent x = 0 ↔ ArchimedeanClass.mk x = 0 := by
  simpa only [leadingExponent_one, ArchimedeanClass.mk_one] using
    leadingExponent_eq_iff hx one_ne_zero

/-- Exact scaling criterion for the finite coefficients in polynomial normalization. -/
theorem finite_div_omegaPower_iff {x : SignSequence.{u}} (hx : x ≠ 0) (a : SignSequence.{u}) :
    IsFinite (x / omegaPower a) ↔ leadingExponent x ≤ a := by
  rw [finite_iff_leadingExponent_nonpos (div_ne_zero hx (omegaPower_ne_zero a)),
    leadingExponent_div hx (omegaPower_ne_zero a), leadingExponent_omegaPower, sub_nonpos]

theorem infinitesimal_div_omegaPower_iff {x : SignSequence.{u}} (hx : x ≠ 0)
    (a : SignSequence.{u}) :
    IsInfinitesimal (x / omegaPower a) ↔ leadingExponent x < a := by
  rw [infinitesimal_iff_leadingExponent_neg (div_ne_zero hx (omegaPower_ne_zero a)),
    leadingExponent_div hx (omegaPower_ne_zero a), leadingExponent_omegaPower, sub_neg]

/-- A scaled nonzero coefficient has nonzero residue exactly at its own growth exponent.
Mathlib's total standard part is zero also on infinite inputs. -/
theorem standardPart_div_omegaPower_ne_zero_iff {x : SignSequence.{u}} (hx : x ≠ 0)
    (a : SignSequence.{u}) :
    standardPart (x / omegaPower a) ≠ 0 ↔ leadingExponent x = a := by
  rw [ne_eq, standardPart, ArchimedeanClass.stdPart_eq_zero, not_not,
    ← leadingExponent_eq_zero_iff (div_ne_zero hx (omegaPower_ne_zero a)),
    leadingExponent_div hx (omegaPower_ne_zero a), leadingExponent_omegaPower, sub_eq_zero]

/-- The chosen monomial represents the same Archimedean class as a nonzero element. -/
theorem archimedeanClass_omegaPower_leadingExponent {x : SignSequence.{u}} (hx : x ≠ 0) :
    ArchimedeanClass.mk (omegaPower (leadingExponent x)) = ArchimedeanClass.mk x := by
  apply (archimedeanClass_toSurreal_eq_iff _ _).mp
  simpa only [toSurreal_omegaPower, toSurreal_leadingExponent] using
    _root_.Surreal.archimedeanClassMk_wpow_wlog (toSurreal_ne_zero hx)

/-- A nonzero element divided by its leading monomial has valuation exactly zero. -/
theorem archimedeanClass_normalized_eq_zero {x : SignSequence.{u}} (hx : x ≠ 0) :
    ArchimedeanClass.mk (x / omegaPower (leadingExponent x)) = 0 := by
  apply (archimedeanClass_toSurreal_eq_zero_iff _).mp
  simpa only [toSurreal_div, toSurreal_omegaPower, toSurreal_leadingExponent] using
    _root_.Surreal.mk_div_wpow_wlog_of_ne_zero (toSurreal_ne_zero hx)

/-- Normalization is finite, including the total value at zero. -/
theorem finite_normalized (x : SignSequence.{u}) :
    IsFinite (x / omegaPower (leadingExponent x)) := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (archimedeanClass_normalized_eq_zero hx).ge

/-- Normalization of a nonzero element retains a nonzero real residue. -/
theorem standardPart_normalized_ne_zero {x : SignSequence.{u}} (hx : x ≠ 0) :
    standardPart (x / omegaPower (leadingExponent x)) ≠ 0 := by
  rw [ne_eq, standardPart, ArchimedeanClass.stdPart_eq_zero, not_not]
  exact archimedeanClass_normalized_eq_zero hx

/-- The real leading coefficient of the actual sign-field element. -/
def leadingCoeff (x : SignSequence.{u}) : ℝ := _root_.Surreal.leadingCoeff (toSurreal x)

/-- The transported leading coefficient is precisely the sign-field standard part. -/
theorem leadingCoeff_eq_standardPart (x : SignSequence.{u}) :
    leadingCoeff x = standardPart (x / omegaPower (leadingExponent x)) := by
  simpa only [leadingCoeff, _root_.Surreal.leadingCoeff, toSurreal_div,
    toSurreal_omegaPower, toSurreal_leadingExponent] using
    standardPart_toSurreal (finite_normalized x)

@[simp] theorem leadingCoeff_zero : leadingCoeff (0 : SignSequence.{u}) = 0 := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_one : leadingCoeff (1 : SignSequence.{u}) = 1 := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_ofReal (r : ℝ) : leadingCoeff (ofReal r : SignSequence.{u}) = r := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_omegaPower (x : SignSequence.{u}) :
    leadingCoeff (omegaPower x) = 1 := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_mul (x y : SignSequence.{u}) :
    leadingCoeff (x * y) = leadingCoeff x * leadingCoeff y := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_neg (x : SignSequence.{u}) : leadingCoeff (-x) = -leadingCoeff x := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_inv (x : SignSequence.{u}) : leadingCoeff x⁻¹ = (leadingCoeff x)⁻¹ := by
  simp [leadingCoeff]

@[simp] theorem leadingCoeff_eq_zero_iff (x : SignSequence.{u}) : leadingCoeff x = 0 ↔ x = 0 := by
  simp [leadingCoeff, ← toSurreal_zero]

@[simp] theorem leadingCoeff_pos_iff (x : SignSequence.{u}) : 0 < leadingCoeff x ↔ 0 < x := by
  simp [leadingCoeff, ← toSurreal_zero]

end

end Surreal.Foundations.SignSequence
