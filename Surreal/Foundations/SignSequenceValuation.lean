import Surreal.Foundations.SignSequenceMonomials

/-!
# The surreal-exponent valuation on the actual sign field

The growth exponent of a nonzero number has the opposite sign from the
documents' valuation exponent. Assigning zero the value infinity makes
this an actual `AddValuation`, equivalent to Mathlib's native Archimedean
valuation. Its value group is the constructed sign field itself, with
its original order and arithmetic. This proves the real-field valuation
prerequisites of `a:eq:valuation` without assuming an infinite Hahn normal
form or a strong-evaluation theorem.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private def valuationValue (x : SignSequence.{u}) : WithTop SignSequence.{u} :=
  if x = 0 then ⊤ else ↑(-leadingExponent x)

private theorem valuationValue_le_iff (x y : SignSequence.{u}) :
    valuationValue x ≤ valuationValue y ↔ ArchimedeanClass.mk x ≤ ArchimedeanClass.mk y := by
  by_cases hx : x = 0
  · subst x
    simp [valuationValue, ArchimedeanClass.mk_eq_top_iff]
  by_cases hy : y = 0
  · subst y
    simp [valuationValue]
  simp only [valuationValue, if_neg hx, if_neg hy, WithTop.coe_le_coe, neg_le_neg_iff]
  exact leadingExponent_le_iff hy hx

private theorem valuationValue_add (x y : SignSequence.{u}) :
    min (valuationValue x) (valuationValue y) ≤ valuationValue (x + y) := by
  rcases le_total (valuationValue x) (valuationValue y) with h | h
  · rw [min_eq_left h, valuationValue_le_iff]
    have h' := (valuationValue_le_iff x y).mp h
    simpa only [min_eq_left h'] using ArchimedeanClass.min_le_mk_add x y
  · rw [min_eq_right h, valuationValue_le_iff]
    have h' := (valuationValue_le_iff y x).mp h
    simpa only [min_eq_right h'] using ArchimedeanClass.min_le_mk_add x y

private theorem valuationValue_mul (x y : SignSequence.{u}) :
    valuationValue (x * y) = valuationValue x + valuationValue y := by
  by_cases hx : x = 0
  · simp [hx, valuationValue]
  by_cases hy : y = 0
  · simp [hy, valuationValue]
  simp [valuationValue, hx, hy, mul_ne_zero hx hy, leadingExponent_mul hx hy, add_comm]

/-- The natural additive valuation, with actual surreal exponents and infinity at zero. -/
def valuation : AddValuation SignSequence.{u} (WithTop SignSequence.{u}) :=
  AddValuation.of valuationValue (by simp [valuationValue])
    (by simp [valuationValue]) valuationValue_add valuationValue_mul

@[simp] theorem valuation_zero : valuation (0 : SignSequence.{u}) = ⊤ := valuation.map_zero
@[simp] theorem valuation_one : valuation (1 : SignSequence.{u}) = 0 := valuation.map_one

theorem valuation_of_ne_zero {x : SignSequence.{u}} (hx : x ≠ 0) :
    valuation x = ↑(-leadingExponent x) := by simp [valuation, valuationValue, hx]

@[simp] theorem valuation_eq_top_iff (x : SignSequence.{u}) : valuation x = ⊤ ↔ x = 0 :=
  valuation.top_iff

theorem valuation_le_iff (x y : SignSequence.{u}) :
    valuation x ≤ valuation y ↔ ArchimedeanClass.mk x ≤ ArchimedeanClass.mk y :=
  valuationValue_le_iff x y

theorem valuation_lt_iff (x y : SignSequence.{u}) :
    valuation x < valuation y ↔ ArchimedeanClass.mk x < ArchimedeanClass.mk y := by
  simp only [lt_iff_not_ge, valuation_le_iff]

theorem valuation_eq_iff (x y : SignSequence.{u}) :
    valuation x = valuation y ↔ ArchimedeanClass.mk x = ArchimedeanClass.mk y := by
  simp only [le_antisymm_iff, valuation_le_iff]

/-- The valuation has exactly the same comparisons as the native Archimedean valuation. -/
theorem valuation_isEquiv_archimedean :
    valuation.IsEquiv (ArchimedeanClass.addValuation SignSequence.{u}) :=
  fun x y => valuation_le_iff y x

theorem valuation_mul (x y : SignSequence.{u}) : valuation (x * y) = valuation x + valuation y :=
  valuation.map_mul x y

theorem min_valuation_le_add (x y : SignSequence.{u}) :
    min (valuation x) (valuation y) ≤ valuation (x + y) := valuation.map_add x y

@[simp] theorem valuation_neg (x : SignSequence.{u}) : valuation (-x) = valuation x :=
  valuation.map_neg x

@[simp] theorem valuation_abs (x : SignSequence.{u}) : valuation |x| = valuation x := by
  apply (valuation_eq_iff _ _).mpr
  exact ArchimedeanClass.mk_abs x

@[simp] theorem valuation_inv (x : SignSequence.{u}) : valuation x⁻¹ = -valuation x :=
  valuation.map_inv

theorem valuation_div (x y : SignSequence.{u}) : valuation (x / y) = valuation x - valuation y :=
  valuation.map_div

theorem valuation_antitone_nonneg {x y : SignSequence.{u}} (hx : 0 ≤ x) (hxy : x ≤ y) :
    valuation y ≤ valuation x :=
  (valuation_le_iff y x).mpr (ArchimedeanClass.mk_antitoneOn hx (hx.trans hxy) hxy)

/-- Valuation sign recovers the already constructed finite-element predicate, including zero. -/
theorem isFinite_iff_valuation_nonneg (x : SignSequence.{u}) : IsFinite x ↔ 0 ≤ valuation x := by
  simpa only [valuation_one, ArchimedeanClass.mk_one, IsFinite] using (valuation_le_iff 1 x).symm

theorem isInfinitesimal_iff_valuation_pos (x : SignSequence.{u}) :
    IsInfinitesimal x ↔ 0 < valuation x := by
  simpa only [valuation_one, ArchimedeanClass.mk_one, IsInfinitesimal] using (valuation_lt_iff 1 x).symm

@[simp] theorem valuation_omegaPower (a : SignSequence.{u}) : valuation (omegaPower a) = ↑(-a) := by
  rw [valuation_of_ne_zero (omegaPower_ne_zero a), leadingExponent_omegaPower]

/-- The source convention `t^a = omega^(-a)`. -/
def tMonomial (a : SignSequence.{u}) : SignSequence.{u} := omegaPower (-a)

theorem tMonomial_pos (a : SignSequence.{u}) : 0 < tMonomial a := omegaPower_pos _
theorem tMonomial_ne_zero (a : SignSequence.{u}) : tMonomial a ≠ 0 := (tMonomial_pos a).ne'

@[simp] theorem tMonomial_zero : tMonomial (0 : SignSequence.{u}) = 1 := by simp [tMonomial]
@[simp] theorem tMonomial_add (a b : SignSequence.{u}) :
    tMonomial (a + b) = tMonomial a * tMonomial b := by simp [tMonomial, mul_comm]
@[simp] theorem tMonomial_neg (a : SignSequence.{u}) : tMonomial (-a) = (tMonomial a)⁻¹ := by
  simp [tMonomial]

@[simp] theorem valuation_tMonomial (a : SignSequence.{u}) : valuation (tMonomial a) = ↑a := by
  simp [tMonomial]

/-- Every surreal exponent occurs as a valuation of a nonzero actual surreal. -/
theorem valuation_surjective : Function.Surjective valuation.{u} := by
  intro a
  cases a with
  | top => exact ⟨0, valuation_zero⟩
  | coe a => exact ⟨tMonomial a, valuation_tMonomial a⟩

/-- A finite element is smaller in absolute value than the infinite Conway monomial. -/
theorem abs_lt_omegaPower_one_of_finite {x : SignSequence.{u}} (hx : IsFinite x) :
    |x| < omegaPower 1 := by
  by_contra h
  have hle := valuation_antitone_nonneg (omegaPower_pos 1).le (le_of_not_gt h)
  rw [valuation_abs, valuation_omegaPower] at hle
  have hneg : ((-(1 : SignSequence.{u})) : WithTop SignSequence.{u}) < 0 :=
    WithTop.coe_lt_coe.mpr (by norm_num)
  exact (hle.trans_lt hneg).not_ge ((isFinite_iff_valuation_nonneg x).mp hx)

end

end Surreal.Foundations.SignSequence
