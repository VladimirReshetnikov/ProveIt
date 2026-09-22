import Surreal.Foundations.SignSequenceValuation
import Surreal.Surcomplex.StandardPart

/-!
# The natural valuation of actual surcomplex numbers

The sign-field valuation of the actual modulus defines a surcomplex
`AddValuation`. This proves the multiplication, sum and modulus identities
of `a:eq:valuation`, and identifies its nonnegative and positive loci with
the already constructed finite ring and infinitesimal ideal. Its value
group consists of the actual surreal exponents; zero has value infinity.
Identification with the least support exponent in an infinite Hahn normal
form remains separate.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The natural valuation, taking actual surreal exponents as values. -/
def valuation : AddValuation Surcomplex.{u} (WithTop SignSequence.{u}) :=
  AddValuation.of (fun z => SignSequence.valuation (modulus z))
    (by simp) (by simp)
    (fun z w => (SignSequence.min_valuation_le_add (modulus z) (modulus w)).trans
      (SignSequence.valuation_antitone_nonneg (modulus_nonneg (z + w)) (modulus_add_le z w)))
    (fun z w => by rw [modulus_mul, SignSequence.valuation_mul])

/-- The modulus clause of `a:eq:valuation` is exact for the constructed modulus. -/
theorem valuation_eq_modulus (z : Surcomplex.{u}) :
    valuation z = SignSequence.valuation (modulus z) := rfl

@[simp] theorem valuation_zero : valuation (0 : Surcomplex.{u}) = ⊤ := valuation.map_zero
@[simp] theorem valuation_one : valuation (1 : Surcomplex.{u}) = 0 := valuation.map_one

@[simp] theorem valuation_eq_top_iff (z : Surcomplex.{u}) : valuation z = ⊤ ↔ z = 0 :=
  valuation.top_iff

theorem valuation_of_ne_zero {z : Surcomplex.{u}} (hz : z ≠ 0) :
    valuation z = ↑(-SignSequence.leadingExponent (modulus z)) :=
  SignSequence.valuation_of_ne_zero ((modulus_eq_zero_iff z).not.mpr hz)

theorem valuation_mul (z w : Surcomplex.{u}) : valuation (z * w) = valuation z + valuation w :=
  valuation.map_mul z w

theorem min_valuation_le_add (z w : Surcomplex.{u}) :
    min (valuation z) (valuation w) ≤ valuation (z + w) := valuation.map_add z w

theorem min_valuation_le_sub (z w : Surcomplex.{u}) :
    min (valuation z) (valuation w) ≤ valuation (z - w) := valuation.map_sub z w

@[simp] theorem valuation_neg (z : Surcomplex.{u}) : valuation (-z) = valuation z :=
  valuation.map_neg z

@[simp] theorem valuation_inv (z : Surcomplex.{u}) : valuation z⁻¹ = -valuation z :=
  valuation.map_inv

theorem valuation_div (z w : Surcomplex.{u}) : valuation (z / w) = valuation z - valuation w :=
  valuation.map_div

@[simp] theorem valuation_conj (z : Surcomplex.{u}) : valuation (conj z) = valuation z := by
  simp only [valuation_eq_modulus, modulus_conj]

/-- The surcomplex valuation restricts to the sign-field valuation on the real axis. -/
@[simp] theorem valuation_ofReal (x : SignSequence.{u}) : valuation (ofReal x) = SignSequence.valuation x := by
  simp only [valuation_eq_modulus, modulus_ofReal, SignSequence.valuation_abs]

theorem valuation_add_of_ne {z w : Surcomplex.{u}} (h : valuation z ≠ valuation w) :
    valuation (z + w) = min (valuation z) (valuation w) := valuation.map_add_of_distinct_val h

/-- The finite valuation ring is exactly the previously constructed modulus-bounded ring. -/
theorem isFinite_iff_valuation_nonneg (z : Surcomplex.{u}) : IsFinite z ↔ 0 ≤ valuation z :=
  (isFinite_iff_modulus z).trans (SignSequence.isFinite_iff_valuation_nonneg (modulus z))

/-- Positive valuation is exactly infinitesimal modulus, with zero included. -/
theorem isInfinitesimal_iff_valuation_pos (z : Surcomplex.{u}) : IsInfinitesimal z ↔ 0 < valuation z :=
  (isInfinitesimal_iff_modulus z).trans (SignSequence.isInfinitesimal_iff_valuation_pos (modulus z))

/-- The source monomials on the actual surcomplex real axis. -/
def tMonomial (a : SignSequence.{u}) : Surcomplex.{u} := ofReal (SignSequence.tMonomial a)

theorem tMonomial_ne_zero (a : SignSequence.{u}) : tMonomial a ≠ 0 :=
  (map_ne_zero ofReal).mpr (SignSequence.tMonomial_ne_zero a)

@[simp] theorem tMonomial_zero : tMonomial (0 : SignSequence.{u}) = 1 := by simp [tMonomial]
@[simp] theorem tMonomial_add (a b : SignSequence.{u}) :
    tMonomial (a + b) = tMonomial a * tMonomial b := by simp [tMonomial]
@[simp] theorem tMonomial_neg (a : SignSequence.{u}) : tMonomial (-a) = (tMonomial a)⁻¹ := by
  simp [tMonomial]

@[simp] theorem modulus_tMonomial (a : SignSequence.{u}) :
    modulus (tMonomial a) = SignSequence.tMonomial a := by
  rw [tMonomial, modulus_ofReal, abs_of_pos (SignSequence.tMonomial_pos a)]

@[simp] theorem valuation_tMonomial (a : SignSequence.{u}) : valuation (tMonomial a) = ↑a := by
  simp [tMonomial]

/-- Every actual surreal exponent occurs; the larger-universe value group is not truncated. -/
theorem valuation_surjective : Function.Surjective valuation.{u} := by
  intro a
  cases a with
  | top => exact ⟨0, valuation_zero⟩
  | coe a => exact ⟨tMonomial a, valuation_tMonomial a⟩

/-- The valuation of a pair is the smaller of its coordinate valuations. -/
theorem valuation_eq_min_coordinates (z : Surcomplex.{u}) :
    valuation z = min (SignSequence.valuation z.re) (SignSequence.valuation z.im) := by
  apply le_antisymm
  · apply le_min
    · simpa only [valuation_eq_modulus, SignSequence.valuation_abs] using
        SignSequence.valuation_antitone_nonneg (abs_nonneg z.re) (abs_re_le_modulus z)
    · simpa only [valuation_eq_modulus, SignSequence.valuation_abs] using
        SignSequence.valuation_antitone_nonneg (abs_nonneg z.im) (abs_im_le_modulus z)
  · have h := (SignSequence.min_valuation_le_add |z.re| |z.im|).trans
      (SignSequence.valuation_antitone_nonneg (modulus_nonneg z) (modulus_le_abs_re_add_abs_im z))
    simpa only [valuation_eq_modulus, SignSequence.valuation_abs] using h

/-- Bundled valuation-ring membership agrees exactly with the existing finite subring. -/
theorem valuationSubring_eq_finiteValuationSubring :
    valuation.toValuation.valuationSubring = finiteValuationSubring.{u} := by
  ext z
  exact (isFinite_iff_valuation_nonneg z).symm

/-- On finite elements, valuation zero is equivalent to a nonzero residue. -/
theorem valuation_eq_zero_iff_standardPart_ne_zero {z : Surcomplex.{u}} (hz : IsFinite z) :
    valuation z = 0 ↔ standardPart z ≠ 0 := by
  rw [ne_eq, standardPart_eq_zero_iff hz, isInfinitesimal_iff_valuation_pos, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h ((isFinite_iff_valuation_nonneg z).mp hz)⟩

/-- Every nonzero ordinary complex constant has valuation zero. -/
theorem valuation_ofComplex {a : ℂ} (ha : a ≠ 0) : valuation (ofComplex a : Surcomplex.{u}) = 0 :=
  (valuation_eq_zero_iff_standardPart_ne_zero (finite_ofComplex a)).mpr
    (by simpa using ha)

/-- Scaling by a monomial turns a valuation lower bound into finiteness. -/
theorem isFinite_div_tMonomial_iff (z : Surcomplex.{u}) (a : SignSequence.{u}) :
    IsFinite (z / tMonomial a) ↔ (a : WithTop SignSequence.{u}) ≤ valuation z := by
  rw [isFinite_iff_valuation_nonneg, valuation_div, valuation_tMonomial]
  cases h : valuation z with
  | top => simp
  | coe b =>
    change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) ≤ ↑(b - a) ↔ ↑a ≤ (b : WithTop SignSequence.{u})
    simp only [WithTop.coe_le_coe, sub_nonneg]

theorem isInfinitesimal_div_tMonomial_iff (z : Surcomplex.{u}) (a : SignSequence.{u}) :
    IsInfinitesimal (z / tMonomial a) ↔ (a : WithTop SignSequence.{u}) < valuation z := by
  rw [isInfinitesimal_iff_valuation_pos, valuation_div, valuation_tMonomial]
  cases h : valuation z with
  | top => simp
  | coe b =>
    change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) < ↑(b - a) ↔ ↑a < (b : WithTop SignSequence.{u})
    simp only [WithTop.coe_lt_coe, sub_pos]

/-- The generous one-exponent modulus estimate `a:lem:valbound`, including zero. -/
theorem modulus_lt_tMonomial_sub_one {z : Surcomplex.{u}} {β : SignSequence.{u}}
    (hβ : (β : WithTop SignSequence.{u}) ≤ valuation z) :
    modulus z < SignSequence.tMonomial (β - 1) := by
  have hf := (isFinite_div_tMonomial_iff z β).mpr hβ
  have hm := (isFinite_iff_modulus (z / tMonomial β)).mp hf
  rw [modulus_div, modulus_tMonomial] at hm
  have hsmall := SignSequence.abs_lt_omegaPower_one_of_finite hm
  rw [abs_of_nonneg (div_nonneg (modulus_nonneg z) (SignSequence.tMonomial_pos β).le)] at hsmall
  have h := (div_lt_iff₀ (SignSequence.tMonomial_pos β)).mp hsmall
  rw [sub_eq_add_neg, SignSequence.tMonomial_add]
  have ht : SignSequence.tMonomial (-1 : SignSequence.{u}) = SignSequence.omegaPower 1 := by
    simp [SignSequence.tMonomial]
  simpa only [ht, mul_comm] using h

end

end Surreal.Surcomplex
