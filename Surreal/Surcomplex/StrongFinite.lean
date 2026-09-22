import Surreal.Surcomplex.StrongAlgebra

/-!
# Agreement of actual strong sums with finite sums

Every finite family is strongly summable. Canonical coefficient summation
then agrees with the existing finite field sum, including the empty family.
The support certificate reuses Mathlib's finite-support Hahn families.
-/

universe u v

namespace Surreal

open Foundations

noncomputable section

namespace Foundations.SignSequence

/-- Every finite actual real family meets both strong summability conditions. -/
theorem stronglySummable_of_finite {ι : Type v} [Finite ι] (f : ι → SignSequence.{u}) :
    StronglySummable f :=
  stronglySummable_of_hahnFamily
    (_root_.HahnSeries.SummableFamily.ofFinsupp
      (Finsupp.equivFunOnFinite.symm (fun i => rawNormalForm (f i)))) (fun _ => rfl)

/-- Strong summation extends the ordinary finite actual real sum. -/
theorem strongSum_eq_sum {ι : Type v} [Fintype ι] (f : ι → SignSequence.{u}) :
    strongSum f (stronglySummable_of_finite f) = ∑ i, f i := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum]
  change _ = rawNormalFormRingHom (∑ i, f i)
  rw [map_sum]
  apply _root_.HahnSeries.ext
  funext a
  simp only [_root_.HahnSeries.SummableFamily.coeff_hsum,
    StronglySummable.toHahnFamily_apply, _root_.HahnSeries.coeff_sum,
    rawNormalFormRingHom_apply, finsum_eq_sum_of_fintype]

end Foundations.SignSequence

namespace Surcomplex

/-- Every finite actual complex family meets both strong summability conditions. -/
theorem stronglySummable_of_finite {ι : Type v} [Finite ι] (f : ι → Surcomplex.{u}) :
    StronglySummable f :=
  stronglySummable_of_hahnFamily
    (_root_.HahnSeries.SummableFamily.ofFinsupp
      (Finsupp.equivFunOnFinite.symm (fun i => rawNormalForm (f i)))) (fun _ => rfl)

/-- Strong summation extends the ordinary finite actual complex sum. -/
theorem strongSum_eq_sum {ι : Type v} [Fintype ι] (f : ι → Surcomplex.{u}) :
    strongSum f (stronglySummable_of_finite f) = ∑ i, f i := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum]
  change _ = rawNormalFormRingHom (∑ i, f i)
  rw [map_sum]
  apply _root_.HahnSeries.ext
  funext a
  simp only [_root_.HahnSeries.SummableFamily.coeff_hsum,
    StronglySummable.toHahnFamily_apply, _root_.HahnSeries.coeff_sum,
    rawNormalFormRingHom_apply, finsum_eq_sum_of_fintype]

end Surcomplex

end

end Surreal
