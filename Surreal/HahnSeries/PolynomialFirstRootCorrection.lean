import Surreal.HahnSeries.StandardPart
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The first coefficient of a simple-root correction

This proves the coefficient identity `polynomial:eq:firstrootcorrection`
without assuming that the ordered exponent group is Archimedean. At a
positive exponent `e`, the error coefficients and the root displacement
are assumed to have order at least `e`. Taylor expansion in the
nonnegative-order Hahn ring makes the quadratic remainder have order
strictly greater than `e`.

The identity allows its numerator and the correction coefficient to vanish.
Existence of the lifted root, and a support argument supplying its order
bound from a least error exponent, are separate results.
-/

namespace Surreal.HahnSeries

open Polynomial
open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The coefficient of evaluation at a constant is the evaluation of the
polynomial formed by the corresponding Hahn coefficients. This identifies
the numerator in the first-correction formula with the source's `E_e(c)`. -/
theorem coeff_eval_constant (E : Polynomial K⟦Γ⟧) (c : K) (g : Γ) :
    (E.eval (single 0 c)).coeff g =
      ∑ n ∈ E.support, (E.coeff n).coeff g * c ^ n := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [single_pow, nsmul_zero, coeff_mul_single_zero]

/-- Evaluating at a coefficient-field constant preserves a common lower
bound on all Hahn coefficient orders. -/
theorem orderTop_eval_constant_ge (E : Polynomial K⟦Γ⟧) (e : Γ)
    (hE : ∀ n, (e : WithTop Γ) ≤ (E.coeff n).orderTop) (c : K) :
    (e : WithTop Γ) ≤ (E.eval (single 0 c)).orderTop := by
  apply le_orderTop_iff_forall.mpr
  intro g hg
  rw [coeff_eval_constant]
  apply Finset.sum_eq_zero
  intro n _
  rw [coeff_eq_zero_of_lt_orderTop (hg.trans_le (hE n)), zero_mul]

/-- Formal differentiation preserves a common Hahn order lower bound. -/
theorem orderTop_derivative_coeff_ge (E : Polynomial K⟦Γ⟧) (e : Γ)
    (hE : ∀ n, (e : WithTop Γ) ≤ (E.coeff n).orderTop) (n : ℕ) :
    (e : WithTop Γ) ≤ (E.derivative.coeff n).orderTop := by
  apply le_orderTop_iff_forall.mpr
  intro g hg
  rw [Polynomial.coeff_derivative]
  have hnat : (n + 1 : K⟦Γ⟧) = single 0 (n + 1 : K) := by
    simp only [← _root_.HahnSeries.C_apply, map_add, map_natCast, map_one]
  rw [hnat, coeff_mul_single_zero,
    coeff_eq_zero_of_lt_orderTop (hg.trans_le (hE (n + 1))), zero_mul]

private theorem exists_nonnegative_taylor_remainder (H : Polynomial K⟦Γ⟧)
    (hH : ∀ n, 0 ≤ (H.coeff n).orderTop) (c : K) (η : K⟦Γ⟧)
    (hη : 0 ≤ η.orderTop) :
    ∃ r : K⟦Γ⟧, 0 ≤ r.orderTop ∧
      r * η ^ 2 + H.derivative.eval (single 0 c) * η + H.eval (single 0 c) =
        H.eval (single 0 c + η) := by
  let f := (nonnegativeSubring Γ K).subtype
  have hlift : H ∈ Polynomial.lifts f :=
    (Polynomial.lifts_iff_coeff_lifts H).mpr fun n => ⟨⟨H.coeff n, hH n⟩, rfl⟩
  obtain ⟨H₀, hH₀⟩ := (Polynomial.mem_lifts H).mp hlift
  obtain ⟨r, hr⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add H₀
    (⟨single 0 c, orderTop_single_le⟩ : nonnegativeSubring Γ K) ⟨η, hη⟩
  refine ⟨r, r.property, ?_⟩
  have h := congrArg f hr
  simp only [map_add, map_mul, map_pow, ← Polynomial.eval_map_apply,
    ← Polynomial.derivative_map, hH₀] at h
  exact h

private theorem coeff_mul_eq_zero_of_order_ge_positive (e : Γ) (he : 0 < e)
    {a b : K⟦Γ⟧} (ha : (e : WithTop Γ) ≤ a.orderTop)
    (hb : (e : WithTop Γ) ≤ b.orderTop) : (a * b).coeff e = 0 := by
  apply coeff_eq_zero_of_lt_orderTop
  apply lt_of_lt_of_le _ (orderTop_add_le_mul (x := a) (y := b))
  apply lt_of_lt_of_le _ (add_le_add ha hb)
  exact_mod_cast (lt_add_of_pos_right e he)

/-- The linear coefficient equation before division by the simple-root
derivative. A root and explicit common order bounds are the only hypotheses. -/
theorem first_root_correction_linear_identity (P₀ : K[X]) (c : K)
    (hc : P₀.IsRoot c) (E : Polynomial K⟦Γ⟧) (e : Γ) (he : 0 < e)
    (hE : ∀ n, (e : WithTop Γ) ≤ (E.coeff n).orderTop)
    (η : K⟦Γ⟧) (hη : (e : WithTop Γ) ≤ η.orderTop)
    (hroot : (P₀.map (_root_.HahnSeries.C : K →+* K⟦Γ⟧) + E).IsRoot (single 0 c + η)) :
    P₀.derivative.eval c * η.coeff e + (E.eval (single 0 c)).coeff e = 0 := by
  let H := P₀.map (_root_.HahnSeries.C : K →+* K⟦Γ⟧) + E
  have he0 : (0 : WithTop Γ) ≤ (e : WithTop Γ) := by exact_mod_cast he.le
  have hH (n : ℕ) : 0 ≤ (H.coeff n).orderTop := by
    simp only [H, Polynomial.coeff_add, Polynomial.coeff_map]
    exact (le_min orderTop_single_le (he0.trans (hE n))).trans min_orderTop_le_orderTop_add
  obtain ⟨r, hr, htaylor⟩ := exists_nonnegative_taylor_remainder H hH c η (he0.trans hη)
  have hquadratic : (r * η ^ 2).coeff e = 0 := by
    rw [pow_two, ← mul_assoc]
    apply coeff_mul_eq_zero_of_order_ge_positive e he _ hη
    calc
      (e : WithTop Γ) = 0 + (e : WithTop Γ) := (zero_add _).symm
      _ ≤ r.orderTop + η.orderTop := add_le_add hr hη
      _ ≤ (r * η).orderTop := orderTop_add_le_mul
  have hderivativeError : (E.derivative.eval (single 0 c) * η).coeff e = 0 :=
    coeff_mul_eq_zero_of_order_ge_positive e he
      (orderTop_eval_constant_ge E.derivative e (orderTop_derivative_coeff_ge E e hE) c) hη
  have hconstant : (P₀.map (_root_.HahnSeries.C : K →+* K⟦Γ⟧)).eval (single 0 c) = 0 := by
    change (P₀.map _).eval (_root_.HahnSeries.C c) = 0
    rw [Polynomial.eval_map_apply, hc.eq_zero, map_zero]
  have hderiv : (P₀.map (_root_.HahnSeries.C : K →+* K⟦Γ⟧)).derivative.eval (single 0 c) =
      single 0 (P₀.derivative.eval c) := by
    rw [Polynomial.derivative_map]
    exact Polynomial.eval_map_apply (p := P₀.derivative)
      (_root_.HahnSeries.C : K →+* K⟦Γ⟧) c
  have hcoeff := congrArg (fun z : K⟦Γ⟧ => z.coeff e) htaylor
  rw [hroot.eq_zero] at hcoeff
  simp only [H, Polynomial.derivative_add, Polynomial.eval_add, hconstant, hderiv,
    zero_add, add_mul, HahnSeries.coeff_add, hquadratic, hderivativeError,
    coeff_single_zero_mul, HahnSeries.coeff_zero, add_zero] at hcoeff
  exact hcoeff

/-- The first-root-correction formula `polynomial:eq:firstrootcorrection`.
It permits cancellation at `e`, including a zero displacement. -/
theorem first_root_correction_coeff (P₀ : K[X]) (c : K) (hc : P₀.IsRoot c)
    (hd : P₀.derivative.eval c ≠ 0) (E : Polynomial K⟦Γ⟧) (e : Γ) (he : 0 < e)
    (hE : ∀ n, (e : WithTop Γ) ≤ (E.coeff n).orderTop)
    (η : K⟦Γ⟧) (hη : (e : WithTop Γ) ≤ η.orderTop)
    (hroot : (P₀.map (_root_.HahnSeries.C : K →+* K⟦Γ⟧) + E).IsRoot (single 0 c + η)) :
    η.coeff e = -(E.eval (single 0 c)).coeff e / P₀.derivative.eval c := by
  apply (eq_div_iff hd).mpr
  have h := first_root_correction_linear_identity P₀ c hc E e he hE η hη hroot
  rw [mul_comm]
  exact eq_neg_of_add_eq_zero_left h

end

end Surreal.HahnSeries
