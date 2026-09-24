import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Standard part in the nonnegative-order Hahn subring

This file proves the algebraic claims in `a:eq:st` and the immediately
following unique decomposition in `docs/surcomplex/analysis/article.tex`.

The subring is Mathlib's ring of integers of `HahnSeries.addVal`, translated
from additive to multiplicative valuation conventions by
`AddValuation.toValuation`. Its elements have `0 ≤ orderTop`. Extraction of
the coefficient at exponent zero is a surjective ring homomorphism, its
kernel consists exactly of positive-order elements, and its residue quotient
is the coefficient field.

The exponent group is an explicit set-sized ordered abelian group. These
results do not identify valuation-nonnegative elements with modulus-bounded
surcomplex numbers and do not construct a surreal normal-form bridge.
-/

namespace Surreal.HahnSeries

noncomputable section

open _root_.HahnSeries

variable (Γ K : Type*) [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The nonnegative-order Hahn subring in `a:eq:st`, using Mathlib's
valuation ring-of-integers construction. -/
def nonnegativeSubring : Subring K⟦Γ⟧ :=
  (AddValuation.toValuation (HahnSeries.addVal Γ K)).integer

variable {Γ K}

/-- The additive-order description of the subring makes the direction of
the valuation convention explicit. -/
@[simp] theorem mem_nonnegativeSubring (x : K⟦Γ⟧) :
    x ∈ nonnegativeSubring Γ K ↔ 0 ≤ x.orderTop := Iff.rfl

omit [IsOrderedAddMonoid Γ] in
/-- On nonnegative-order series, the constant coefficient vanishes exactly
when the order is strictly positive. Zero has order `⊤` and is included. -/
theorem coeff_zero_eq_zero_iff_orderTop_pos (x : K⟦Γ⟧) (hx : 0 ≤ x.orderTop) :
    x.coeff 0 = 0 ↔ 0 < x.orderTop := by
  refine ⟨fun h => lt_of_le_of_ne hx ?_, coeff_eq_zero_of_lt_orderTop⟩
  exact (orderTop_ne_of_coeff_eq_zero h).symm

/-- Constant-coefficient extraction is multiplicative when neither factor
has negative exponents. This supplies the multiplicative part of `a:eq:st`. -/
theorem coeff_zero_mul_of_nonnegative (x y : K⟦Γ⟧)
    (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  by_cases hxc : x.coeff 0 = 0
  · rw [hxc, zero_mul]
    apply coeff_eq_zero_of_lt_orderTop
    rw [orderTop_mul]
    exact add_pos_of_pos_of_nonneg ((coeff_zero_eq_zero_iff_orderTop_pos x hx).mp hxc) hy
  by_cases hyc : y.coeff 0 = 0
  · rw [hyc, mul_zero]
    apply coeff_eq_zero_of_lt_orderTop
    rw [orderTop_mul]
    rw [add_comm]
    exact add_pos_of_pos_of_nonneg ((coeff_zero_eq_zero_iff_orderTop_pos y hy).mp hyc) hx
  have hxo : x.order = 0 := le_antisymm (order_le_of_coeff_ne_zero hxc)
    (zero_le_orderTop_iff.mp hx)
  have hyo : y.order = 0 := le_antisymm (order_le_of_coeff_ne_zero hyc)
    (zero_le_orderTop_iff.mp hy)
  simpa only [hxo, hyo, zero_add, leadingCoeff_eq] using coeff_mul_order_add_order x y

variable (Γ K)

/-- Standard part as the coefficient-zero ring homomorphism in `a:eq:st`. -/
def standardPart : nonnegativeSubring Γ K →+* K where
  toFun x := (x : K⟦Γ⟧).coeff 0
  map_one' := by change (1 : K⟦Γ⟧).coeff 0 = 1; simp
  map_mul' x y := coeff_zero_mul_of_nonnegative (x : K⟦Γ⟧) (y : K⟦Γ⟧)
    ((mem_nonnegativeSubring _).mp x.property) ((mem_nonnegativeSubring _).mp y.property)
  map_zero' := coeff_zero
  map_add' x y := coeff_add

variable {Γ K}

@[simp] theorem standardPart_apply (x : nonnegativeSubring Γ K) :
    standardPart Γ K x = (x : K⟦Γ⟧).coeff 0 := rfl

/-- Constants give every residue class, proving the surjectivity in
`a:eq:st`. -/
theorem standardPart_surjective : Function.Surjective (standardPart Γ K) := by
  intro a
  exact ⟨⟨single 0 a, (mem_nonnegativeSubring _).mpr orderTop_single_le⟩, coeff_single_same 0 a⟩

variable (Γ K)

/-- The ideal of positive-order elements, realized as the kernel of
standard part in `a:eq:st`. -/
def infinitesimalIdeal : Ideal (nonnegativeSubring Γ K) :=
  RingHom.ker (standardPart Γ K)

variable {Γ K}

/-- Membership in the standard-part kernel is exactly positive order. -/
@[simp] theorem mem_infinitesimalIdeal (x : nonnegativeSubring Γ K) :
    x ∈ infinitesimalIdeal Γ K ↔ 0 < (x : K⟦Γ⟧).orderTop := by
  change (x : K⟦Γ⟧).coeff 0 = 0 ↔ _
  exact coeff_zero_eq_zero_iff_orderTop_pos (x : K⟦Γ⟧)
    ((mem_nonnegativeSubring _).mp x.property)

/-- The infinitesimal ideal is maximal, as claimed just before `a:eq:st`. -/
theorem infinitesimalIdeal_isMaximal : (infinitesimalIdeal Γ K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (standardPart Γ K) standardPart_surjective

variable (Γ K)

/-- The residue-field identification in `a:eq:st`, obtained from Mathlib's
first isomorphism theorem for rings. -/
def residueEquiv : (nonnegativeSubring Γ K) ⧸ infinitesimalIdeal Γ K ≃+* K :=
  RingHom.quotientKerEquivOfSurjective standardPart_surjective

variable {Γ K}

/-- The quotient isomorphism sends the class of `x` to its zero coefficient. -/
@[simp] theorem residueEquiv_mk (x : nonnegativeSubring Γ K) :
    residueEquiv Γ K (Ideal.Quotient.mk (infinitesimalIdeal Γ K) x) =
      standardPart Γ K x := rfl

/-- Subtracting the constant coefficient leaves positive order. -/
theorem orderTop_sub_standardPart_pos (x : nonnegativeSubring Γ K) :
    0 < ((x : K⟦Γ⟧) - single 0 (standardPart Γ K x)).orderTop := by
  apply (coeff_zero_eq_zero_iff_orderTop_pos _ ?_).mp
  · simp only [coeff_sub, coeff_single_same, standardPart_apply, sub_self]
  · exact (le_min ((mem_nonnegativeSubring _).mp x.property) orderTop_single_le).trans
      min_orderTop_le_orderTop_sub

/-- The unique constant-plus-infinitesimal decomposition following
`a:eq:st`. Both the constant and the positive-order remainder are unique. -/
theorem exists_unique_standardPart_decomposition (x : nonnegativeSubring Γ K) :
    ∃! ae : K × K⟦Γ⟧, (x : K⟦Γ⟧) = single 0 ae.1 + ae.2 ∧ 0 < ae.2.orderTop := by
  refine ⟨(standardPart Γ K x, (x : K⟦Γ⟧) - single 0 (standardPart Γ K x)),
    ⟨?_, orderTop_sub_standardPart_pos x⟩, ?_⟩
  · simp only [← add_sub_assoc, add_sub_cancel_left]
  rintro ⟨a, ε⟩ ⟨h, hε⟩
  have ha : standardPart Γ K x = a := by
    rw [standardPart_apply]
    have hεc : ε.coeff 0 = 0 := coeff_eq_zero_of_lt_orderTop hε
    have hc := congrArg (fun z : K⟦Γ⟧ => z.coeff 0) h
    simpa only [coeff_add, coeff_single_same, hεc,
      add_zero] using hc
  apply Prod.ext ha.symm
  change ε = (x : K⟦Γ⟧) - single 0 (standardPart Γ K x)
  rw [ha, h, add_sub_cancel_left]

end

end Surreal.HahnSeries
