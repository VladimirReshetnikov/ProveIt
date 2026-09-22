import Surreal.Foundations.SmallNormalFormTruncation

/-!
# The boundary of a product of formal normal forms

At a sum of supported growth exponents, the two factor tails have their
greatest terms at those exponents. Their product has no terms above the sum
and its coefficient there is the product of the two boundary coefficients.
Consequently products involving the earlier truncations determine all
strictly earlier terms of the full product. Evaluation is not used.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

noncomputable section

private abbrev hahnExponent (a : SignSequence.{u}) : _root_.Surreal.{u}ᵒᵈ :=
  OrderDual.toDual (SignSequence.toSurreal a)

/-- Every supported product exponent is the sum of supported factor exponents. -/
theorem exists_add_eq_of_mem_support_mul (F G : SmallNormalForm.{u})
    {c : SignSequence.{u}} (hc : c ∈ support (F * G)) :
    ∃ a ∈ support F, ∃ b ∈ support G, a + b = c := by
  have hc' : hahnExponent c ∈ ((ofLex F.val) * (ofLex G.val)).support := hc
  obtain ⟨a, ha, b, hb, hab⟩ := _root_.HahnSeries.support_mul_subset hc'
  refine ⟨SignSequence.toSurrealOrderIso.symm (OrderDual.ofDual a), ?_,
    SignSequence.toSurrealOrderIso.symm (OrderDual.ofDual b), ?_, ?_⟩
  · change _root_.SurrealHahnSeries.coeff F
      (SignSequence.toSurreal (SignSequence.toSurrealOrderIso.symm (OrderDual.ofDual a))) ≠ 0
    rw [SignSequence.toSurreal_orderIso_symm]
    exact ha
  · change _root_.SurrealHahnSeries.coeff G
      (SignSequence.toSurreal (SignSequence.toSurrealOrderIso.symm (OrderDual.ofDual b))) ≠ 0
    rw [SignSequence.toSurreal_orderIso_symm]
    exact hb
  · apply (SignSequence.toSurreal_inj _ _).mp
    rw [SignSequence.toSurreal_add, SignSequence.toSurreal_orderIso_symm,
      SignSequence.toSurreal_orderIso_symm]
    exact congrArg OrderDual.ofDual hab

@[simp] theorem coeff_sub_trunc_self (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    coeff (F - trunc F a) a = coeff F a := by
  simp [coeff_sub]

/-- A tail contains no growth exponent above its cutoff. -/
theorem le_of_mem_support_sub_trunc (F : SmallNormalForm.{u}) (a : SignSequence.{u})
    {b : SignSequence.{u}} (hb : b ∈ support (F - trunc F a)) : b ≤ a := by
  by_contra! hab
  have hz : coeff (F - trunc F a) b = 0 := by
    rw [coeff_sub, coeff_trunc_of_lt F hab, sub_self]
  exact hb hz

private theorem hahn_orderTop_sub_trunc (F : SmallNormalForm.{u})
    {a : SignSequence.{u}} (ha : a ∈ support F) :
    (ofLex (F - trunc F a).val).orderTop =
      (hahnExponent a : WithTop (_root_.Surreal.{u}ᵒᵈ)) := by
  apply _root_.HahnSeries.orderTop_eq_of_le
  · change coeff (F - trunc F a) a ≠ 0
    rw [coeff_sub_trunc_self]
    exact (mem_support F a).mp ha
  · intro b hb
    let b' := SignSequence.toSurrealOrderIso.symm (OrderDual.ofDual b)
    have hb' : b' ∈ support (F - trunc F a) := by
      change _root_.SurrealHahnSeries.coeff (F - trunc F a)
        (SignSequence.toSurreal b') ≠ 0
      rw [SignSequence.toSurreal_orderIso_symm]
      exact hb
    have hle := (SignSequence.toSurreal_le_iff b' a).mpr
      (le_of_mem_support_sub_trunc F a hb')
    change OrderDual.ofDual b ≤ SignSequence.toSurreal a
    simpa only [b', SignSequence.toSurreal_orderIso_symm] using hle

/-- The product of two tails has no exponent above the sum of their cutoffs. -/
theorem trunc_tail_mul_zero (F G : SmallNormalForm.{u}) (a b : SignSequence.{u}) :
    trunc ((F - trunc F a) * (G - trunc G b)) (a + b) = 0 := by
  apply trunc_eq_zero_of_no_support_gt
  intro c hc
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_add_eq_of_mem_support_mul _ _ hc
  exact add_le_add (le_of_mem_support_sub_trunc F a hp)
    (le_of_mem_support_sub_trunc G b hq)

/-- Native Hahn leading-coefficient multiplication computes the product-tail boundary. -/
theorem coeff_tail_mul_add (F G : SmallNormalForm.{u}) {a b : SignSequence.{u}}
    (ha : a ∈ support F) (hb : b ∈ support G) :
    coeff ((F - trunc F a) * (G - trunc G b)) (a + b) = coeff F a * coeff G b := by
  let R := ofLex (F - trunc F a).val
  let S := ofLex (G - trunc G b).val
  have hR := hahn_orderTop_sub_trunc F ha
  have hS := hahn_orderTop_sub_trunc G hb
  have hRS : (R * S).orderTop =
      (hahnExponent (a + b) : WithTop (_root_.Surreal.{u}ᵒᵈ)) := by
    rw [_root_.HahnSeries.orderTop_mul, hR, hS, ← WithTop.coe_add]
    congr 1
    exact (congrArg OrderDual.toDual (SignSequence.toSurreal_add a b)).symm
  have hm := _root_.HahnSeries.leadingCoeff_mul R S
  unfold _root_.HahnSeries.leadingCoeff at hm
  rw [hRS, hR, hS] at hm
  change coeff ((F - trunc F a) * (G - trunc G b)) (a + b) =
    coeff (F - trunc F a) a * coeff (G - trunc G b) b at hm
  simpa only [coeff_sub_trunc_self] using hm

/-- Products involving an earlier factor determine the strict earlier product truncation. -/
theorem trunc_product_frontier (F G : SmallNormalForm.{u}) (a b : SignSequence.{u}) :
    trunc (F * G) (a + b) =
      trunc (trunc F a * G + F * trunc G b - trunc F a * trunc G b) (a + b) := by
  have he : F * G =
      (trunc F a * G + F * trunc G b - trunc F a * trunc G b) +
        (F - trunc F a) * (G - trunc G b) := by ring
  rw [he]
  rw [show trunc
      ((trunc F a * G + F * trunc G b - trunc F a * trunc G b) +
        (F - trunc F a) * (G - trunc G b)) (a + b) =
      trunc (trunc F a * G + F * trunc G b - trunc F a * trunc G b) (a + b) +
        trunc ((F - trunc F a) * (G - trunc G b)) (a + b) from
      _root_.SurrealHahnSeries.trunc_add _ _ _]
  rw [trunc_tail_mul_zero, add_zero]

/-- The omitted product-tail contribution at the boundary is one coefficient product. -/
theorem coeff_product_frontier (F G : SmallNormalForm.{u}) {a b : SignSequence.{u}}
    (ha : a ∈ support F) (hb : b ∈ support G) :
    coeff (F * G) (a + b) =
      coeff (trunc F a * G + F * trunc G b - trunc F a * trunc G b) (a + b) +
        coeff F a * coeff G b := by
  have he : F * G =
      (trunc F a * G + F * trunc G b - trunc F a * trunc G b) +
        (F - trunc F a) * (G - trunc G b) := by ring
  rw [he, coeff_add, coeff_tail_mul_add F G ha hb]

end

end Surreal.Foundations.SmallNormalForm
