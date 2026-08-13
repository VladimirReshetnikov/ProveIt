import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

/-- The exact base-field obstruction used in Lazard's nonvanishing argument:
`-1` is not a square in `F`. -/
def MinusOneNonsquare (F : Type*) [Field F] : Prop :=
  ¬ ∃ q : F, q ^ 2 = -(1 : F)

/-- If the ratio `a / b` descends to a field in which `-1` is not a square,
then `a² + b²` cannot vanish.  This is the algebraic core of Lazard's
argument, independent of any particular quintic invariant or Galois action. -/
theorem sq_add_sq_ne_zero_of_ratio_mem_range_of_minusOneNonsquare
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (hns : MinusOneNonsquare F)
    (a b : L) (hb : b ≠ 0)
    (hbase : a / b ∈ Set.range (algebraMap F L)) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := hbase
  have hratio : (a / b) ^ 2 = -(1 : L) := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hb)).2
    linear_combination hzero
  have hq_square : q ^ 2 = -(1 : F) := by
    apply (algebraMap F L).injective
    simpa only [map_pow, map_neg, map_one, hq] using hratio
  exact hns ⟨q, hq_square⟩

/-- Galois-fixed form of
`sq_add_sq_ne_zero_of_ratio_mem_range_of_minusOneNonsquare`: the fixed-field
theorem supplies the descent of `a / b` to the base field. -/
theorem sq_add_sq_ne_zero_of_galois_fixed_ratio_of_minusOneNonsquare
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (hns : MinusOneNonsquare F)
    (a b : L) (hb : b ≠ 0)
    (hfixed : ∀ σ : L ≃ₐ[F] L, σ (a / b) = a / b) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  apply sq_add_sq_ne_zero_of_ratio_mem_range_of_minusOneNonsquare hns a b hb
  exact
    (IsGalois.mem_range_algebraMap_iff_fixed
      (F := F) (E := L) (a / b)).2 hfixed

end LeanProofs.PolynomialFormulas.LazardQuintic
