import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughParts
import Mathlib.Data.Nat.Factorial.Basic

/-!
# One finite quotient for bounded ideal computations

The quotient modulo the square of the factorial of the norm bound
contains exact images of every relevant ideal and of all their pairwise
products. Its ideals therefore suffice for incidence, divisibility, and
midpoint tests in the original number field.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The common modulus for ideal comparisons through norm `H`. -/
def boundedIdealModulus (K : Type*) [Field K] [NumberField K] (H : ℕ) : Ideal (𝓞 K) :=
  Ideal.span {((H.factorial^2 : ℕ) : 𝓞 K)}

private theorem factorial_mem_of_absNorm_le {H : ℕ} {I : (Ideal (𝓞 K))⁰}
    (hI : absNorm I.val ≤ H) : (H.factorial : 𝓞 K) ∈ I.val := by
  obtain ⟨d,hd⟩ := Nat.dvd_factorial (absNorm_pos_of_nonZeroDivisors I) hI
  rw [hd, Nat.cast_mul]
  exact I.val.mul_mem_right _ (absNorm_mem I.val)

theorem boundedIdealModulus_le (H : ℕ) {I : (Ideal (𝓞 K))⁰} (hI : absNorm I.val ≤ H) :
    boundedIdealModulus K H ≤ I.val := by
  rw [boundedIdealModulus, Ideal.span_singleton_le_iff_mem, Nat.cast_pow, pow_two]
  exact I.val.mul_mem_right _ (factorial_mem_of_absNorm_le hI)

theorem boundedIdealModulus_le_mul (H : ℕ) {I J : (Ideal (𝓞 K))⁰}
    (hI : absNorm I.val ≤ H) (hJ : absNorm J.val ≤ H) :
    boundedIdealModulus K H ≤ (I*J).val := by
  rw [boundedIdealModulus, Ideal.span_singleton_le_iff_mem, Nat.cast_pow, pow_two, Submonoid.coe_mul]
  exact Ideal.mul_mem_mul (factorial_mem_of_absNorm_le hI) (factorial_mem_of_absNorm_le hJ)

/-- Equality of tested ideals is reflected by the common finite quotient. -/
theorem boundedIdeal_map_eq_iff (H : ℕ) {I J : Ideal (𝓞 K)}
    (hI : boundedIdealModulus K H ≤ I) (hJ : boundedIdealModulus K H ≤ J) :
    I.map (Ideal.Quotient.mk (boundedIdealModulus K H)) =
      J.map (Ideal.Quotient.mk (boundedIdealModulus K H)) ↔ I = J := by
  constructor
  · intro h
    have he := congrArg (Ideal.comap (Ideal.Quotient.mk (boundedIdealModulus K H))) h
    rwa [Ideal.comap_map_mk hI, Ideal.comap_map_mk hJ] at he
  · rintro rfl
    rfl

/-- Containment, hence divisibility in reverse order, is also reflected. -/
theorem boundedIdeal_map_le_iff (H : ℕ) {I J : Ideal (𝓞 K)}
    (hI : boundedIdealModulus K H ≤ I) (hJ : boundedIdealModulus K H ≤ J) :
    I.map (Ideal.Quotient.mk (boundedIdealModulus K H)) ≤
      J.map (Ideal.Quotient.mk (boundedIdealModulus K H)) ↔ I ≤ J := by
  constructor
  · intro h
    have he := Ideal.comap_mono (f := Ideal.Quotient.mk (boundedIdealModulus K H)) h
    rwa [Ideal.comap_map_mk hI, Ideal.comap_map_mk hJ] at he
  · exact Ideal.map_mono

/-- The original norm is the exact cardinality of the quotient by the
represented ideal in the common modulus ring. -/
theorem boundedIdeal_quotient_card (H : ℕ) {I : Ideal (𝓞 K)} (hI : boundedIdealModulus K H ≤ I) :
    Nat.card (((𝓞 K) ⧸ boundedIdealModulus K H) ⧸ I.map (Ideal.Quotient.mk (boundedIdealModulus K H))) =
      absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hI).toEquiv

/-- Every abstract quotient ideal lifts to a nonzero ideal in the number field. -/
theorem boundedIdeal_comap_ne_bot (H : ℕ) (J : Ideal ((𝓞 K) ⧸ boundedIdealModulus K H)) :
    J.comap (Ideal.Quotient.mk (boundedIdealModulus K H)) ≠ ⊥ := by
  intro h
  have hm : ((H.factorial^2 : ℕ) : 𝓞 K) ∈ J.comap (Ideal.Quotient.mk (boundedIdealModulus K H)) := by
    change Ideal.Quotient.mk (boundedIdealModulus K H) ((H.factorial^2 : ℕ) : 𝓞 K) ∈ J
    have hzero : Ideal.Quotient.mk (boundedIdealModulus K H) ((H.factorial^2 : ℕ) : 𝓞 K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hzero]
    exact J.zero_mem
  rw [h, Ideal.mem_bot] at hm
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.factorial_ne_zero _))) hm

end GRHArticle.ProgressionFree.NumberFieldIdeals
