import CombinatorialGames.Surreal.HahnSeries.Basic
import Surreal.Foundations.SignSequenceMonomials

/-!
# Small formal normal forms with actual surreal exponents

The pinned upstream small-support Hahn field supplies a formal carrier and
ordinal truncation recursion. This interface labels its growth exponents by
the constructed sign field using the proved sign/game order equivalence.
Support is explicitly small in the lower universe and reverse well ordered.

This is formal normal-form data, not an evaluation into the actual sign
field. The exponent convention here is decreasing `omegaPower` exponents,
as in `found:eq:normalform`, rather than increasing `tMonomial` exponents.
-/

universe u

namespace Surreal.Foundations

noncomputable section

/-- The formal ordered field of lower-universe-small normal forms. -/
abbrev SmallNormalForm : Type (u + 1) := _root_.SurrealHahnSeries.{u}

namespace SmallNormalForm

/-- Coefficients indexed by actual sign-sequence growth exponents. -/
def coeff (F : SmallNormalForm.{u}) (a : SignSequence.{u}) : ℝ :=
  _root_.SurrealHahnSeries.coeff F (SignSequence.toSurreal a)

/-- The nonzero growth exponents of a formal normal form. -/
def support (F : SmallNormalForm.{u}) : Set SignSequence.{u} := Function.support (coeff F)

@[simp] theorem mem_support (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    a ∈ support F ↔ coeff F a ≠ 0 := Iff.rfl

/-- Changing from game exponents to sign exponents preserves smallness. -/
instance small_support (F : SmallNormalForm.{u}) : Small.{u} (support F) := by
  let f : support F → (_root_.SurrealHahnSeries.support F) := fun a => ⟨SignSequence.toSurreal a.val, a.property⟩
  apply small_of_injective (f := f)
  intro a b h
  apply Subtype.ext
  exact (SignSequence.toSurreal_inj _ _).mp (congrArg Subtype.val h)

/-- Growth exponents decrease along the support's well order. -/
theorem wellFoundedOn_support (F : SmallNormalForm.{u}) :
    (support F).WellFoundedOn (· > ·) := by
  let e : (· > · : support F → support F → Prop) ↪r (· > · : (_root_.SurrealHahnSeries.support F) → (_root_.SurrealHahnSeries.support F) → Prop) :=
    { toFun a := ⟨SignSequence.toSurreal a.val, a.property⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact (SignSequence.toSurreal_inj _ _).mp (congrArg Subtype.val h)
      map_rel_iff' := SignSequence.toSurreal_lt_iff _ _ }
  exact e.wellFounded (_root_.SurrealHahnSeries.wellFoundedOn_support F)

@[ext] theorem ext {F G : SmallNormalForm.{u}} (h : ∀ a, coeff F a = coeff G a) : F = G := by
  apply _root_.SurrealHahnSeries.ext
  funext a
  obtain ⟨b, rfl⟩ := SignSequence.toSurreal_surjective a
  exact h b

/-- The lower-universe ordinal length of the support. -/
abbrev length (F : SmallNormalForm.{u}) : Ordinal.{u} := _root_.SurrealHahnSeries.length F

@[simp] theorem length_eq_zero (F : SmallNormalForm.{u}) : length F = 0 ↔ F = 0 :=
  _root_.SurrealHahnSeries.length_eq_zero

/-- The actual growth exponent at a valid ordinal index. -/
def exponent (F : SmallNormalForm.{u}) (i : Set.Iio (length F)) : SignSequence.{u} :=
  SignSequence.toSurrealOrderIso.symm (F.exp i).val

theorem exponent_strictAnti (F : SmallNormalForm.{u}) : StrictAnti (exponent F) := by
  intro i j hij
  exact SignSequence.toSurrealOrderIso.symm.strictMono (F.exp_strictAnti hij)

/-- The coefficient at an ordinal index; it is zero past the support length. -/
abbrev coefficientAt (F : SmallNormalForm.{u}) (i : Ordinal.{u}) : ℝ := F.coeffIdx i

@[simp] theorem coeff_exponent (F : SmallNormalForm.{u}) (i : Set.Iio (length F)) :
    coeff F (exponent F i) = coefficientAt F i := by
  simp only [coeff, exponent, SignSequence.toSurreal_orderIso_symm, coefficientAt,
    _root_.SurrealHahnSeries.coeff_exp]

@[simp] theorem coefficientAt_eq_zero (F : SmallNormalForm.{u}) (i : Ordinal.{u}) :
    coefficientAt F i = 0 ↔ length F ≤ i := _root_.SurrealHahnSeries.coeffIdx_eq_zero_iff

theorem exponent_mem_support (F : SmallNormalForm.{u}) (i : Set.Iio (length F)) :
    exponent F i ∈ support F := by
  rw [mem_support, coeff_exponent, ne_eq, coefficientAt_eq_zero]
  exact not_le_of_gt i.property

theorem exists_exponent_of_mem_support (F : SmallNormalForm.{u}) {a : SignSequence.{u}}
    (ha : a ∈ support F) : ∃ i : Set.Iio (length F), exponent F i = a := by
  obtain ⟨i, hi⟩ := _root_.SurrealHahnSeries.eq_exp_of_mem_support (x := F)
    (i := SignSequence.toSurreal a) ha
  refine ⟨i, ?_⟩
  simp only [exponent, hi, SignSequence.orderIso_symm_toSurreal]

/-- One term is an actual Conway monomial; this does not evaluate the full series. -/
def term (F : SmallNormalForm.{u}) (i : Ordinal.{u}) : SignSequence.{u} :=
  SignSequence.toSurrealOrderIso.symm (_root_.SurrealHahnSeries.term F i)

theorem term_of_lt (F : SmallNormalForm.{u}) {i : Ordinal.{u}} (hi : i < length F) :
    term F i = SignSequence.ofReal (coefficientAt F i) *
      SignSequence.omegaPower (exponent F ⟨i, hi⟩) := by
  apply (SignSequence.toSurreal_inj _ _).mp
  simp only [term, SignSequence.toSurreal_orderIso_symm,
    _root_.SurrealHahnSeries.term_of_lt hi, SignSequence.toSurreal_mul,
    SignSequence.toSurreal_ofReal, SignSequence.toSurreal_omegaPower,
    exponent, SignSequence.toSurreal_orderIso_symm, coefficientAt]

@[simp] theorem term_eq_zero (F : SmallNormalForm.{u}) (i : Ordinal.{u}) :
    term F i = 0 ↔ length F ≤ i := by
  rw [← SignSequence.toSurreal_inj]
  simp only [term, SignSequence.toSurreal_orderIso_symm, SignSequence.toSurreal_zero,
    _root_.SurrealHahnSeries.term_eq_zero]

/-- Keep only growth exponents strictly greater than the specified exponent. -/
def trunc (F : SmallNormalForm.{u}) (a : SignSequence.{u}) : SmallNormalForm.{u} :=
  _root_.SurrealHahnSeries.trunc F (SignSequence.toSurreal a)

@[simp] theorem coeff_trunc (F : SmallNormalForm.{u}) (a b : SignSequence.{u}) :
    coeff (trunc F a) b = if a < b then coeff F b else 0 := by
  simp only [coeff, trunc, _root_.SurrealHahnSeries.coeff_trunc,
    SignSequence.toSurreal_lt_iff]

theorem length_trunc_lt (F : SmallNormalForm.{u}) {a : SignSequence.{u}}
    (ha : a ∈ support F) : length (trunc F a) < length F :=
  _root_.SurrealHahnSeries.length_trunc_lt ha

/-- Truncate at an ordinal support index, with the full series past its length. -/
abbrev truncIdx (F : SmallNormalForm.{u}) (i : Ordinal.{u}) : SmallNormalForm.{u} := _root_.SurrealHahnSeries.truncIdx F i

@[simp] theorem length_truncIdx (F : SmallNormalForm.{u}) (i : Ordinal.{u}) :
    length (truncIdx F i) = min i (length F) := _root_.SurrealHahnSeries.length_truncIdx F i

theorem length_truncIdx_lt (F : SmallNormalForm.{u}) {i : Ordinal.{u}} (hi : i < length F) :
    length (truncIdx F i) < length F := by rw [length_truncIdx, min_eq_left hi.le]; exact hi

theorem truncIdx_of_length_le (F : SmallNormalForm.{u}) {i : Ordinal.{u}} (hi : length F ≤ i) :
    truncIdx F i = F := _root_.SurrealHahnSeries.truncIdx_of_le hi

theorem truncIdx_eq_trunc (F : SmallNormalForm.{u}) (i : Set.Iio (length F)) :
    truncIdx F i = trunc F (exponent F i) := by
  simp only [truncIdx, trunc, exponent, SignSequence.toSurreal_orderIso_symm,
    _root_.SurrealHahnSeries.trunc_exp]

end SmallNormalForm

end
end Surreal.Foundations
