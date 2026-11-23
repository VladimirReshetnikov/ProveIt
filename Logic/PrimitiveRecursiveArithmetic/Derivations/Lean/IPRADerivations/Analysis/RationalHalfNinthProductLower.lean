import IPRADerivations.Analysis.RationalConvexEndpointBudget
import IPRADerivations.Analysis.GaussianPositiveRealArithmetic
import IPRADerivations.Analysis.RationalCubeInfimumIntervals

/-!
# The finite half-times-ninth lower bound with observation errors

Shift each lower endpoint by its actual rational allowance. At U>=18
both shifted endpoints are nonnegative. Original rational monotonicity
then bounds the actual product, spending only one copy of 1/U.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalHalfNinthProductLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction)
open RationalArithmetic (add negative multiply)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def lowered (m U : PTm n) : PTm n := add (fraction one m) (negative (fraction one U))

theorem add_negative_cancel (a e : PTm n) (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a) : Γ ⊢[PRAAx]
    add (add a e) (negative e) ≐ a := by
  have rep := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _ (RationalArithmetic.add_value a e) (RationalArithmetic.negative_value e)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _) ha rep
    (RationalRepresentations.represents_self a)
    (positive_product _ _ (RationalArithmetic.product_denominator_positive a e) (RationalArgmin.denominator_positive e))
    (RationalArgmin.denominator_positive a)
  apply ZT.derive
  simp only [RationalArithmetic.addNumerator,RationalArithmetic.productDenominator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem lowered_below (m U r : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hr : Γ ⊢[PRAAx] RationalNormalForm.wellFormed r)
    (h : Γ ⊢[PRAAx] upper (fraction one m) r one U) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (lowered m U) r := by
  have order := RationalConvexEndpointBudget.order_of_upper _ _ one U hU h
  have shifted := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ order
    (RationalArgmin.reflexive (negative (fraction one U)))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (add_negative_cancel r (fraction one U) hr) shifted

theorem lowered_represents (m U : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hU : Γ ⊢[PRAAx] le one U) (hmu : Γ ⊢[PRAAx] le m U) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (lowered m U) (ZT.ofNat (monus U m)) (m*U) := by
  have c := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat one) m hm
  have e := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat one) U hU
  have sum := RationalRepresentations.represents_add _ _ _ _ _ _ c (RationalRepresentations.represents_negative _ _ _ e)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) sum
  apply ZT.derive
  have eq := natEq (eq_add_of_le hmu)
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat]
  ipra_simps
  linear_combination eq

theorem lowered_sign (m U : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hU : Γ ⊢[PRAAx] le one U) (hmu : Γ ⊢[PRAAx] le m U) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.sign (lowered m U) :=
  GaussianRationalL1.nonnegative_of_representation _ _ _ (positive_product _ _ hm hU) (lowered_represents m U hm hU hmu)

theorem lowered_product_error (U : PTm n) (hU : Γ ⊢[PRAAx] le (num 18) U) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (multiply (lowered two U) (lowered (num 9) U)) one U := by
  have h1 : Γ ⊢[PRAAx] le one U := le_trans (le_of_eq_add (d := num 17) (by ipra_ring)) hU
  have h2 : Γ ⊢[PRAAx] le two U := le_trans (le_of_eq_add (d := num 16) (by ipra_ring)) hU
  have h9 : Γ ⊢[PRAAx] le (num 9) U := le_trans (le_of_eq_add (d := num 9) (by ipra_ring)) hU
  have nine : Γ ⊢[PRAAx] le one (num 9) := le_of_eq_add (d := num 8) (by ipra_ring)
  have eighteen : Γ ⊢[PRAAx] le one (num 18) := le_of_eq_add (d := num 17) (by ipra_ring)
  have prod := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (lowered_represents two U (le_succ_self one) h1 h2) (lowered_represents (num 9) U nine h1 h9)
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat one)
    (ZT.ofNat (monus U two)*ZT.ofNat (monus U (num 9))) (num 18) ((two*U)*((num 9)*U)) one U
    eighteen (positive_product _ _ (positive_product _ _ (le_succ_self one) h1) (positive_product _ _ nine h1))
    (RationalIntegerNormalization.normalize_preserves_value _ _ eighteen) prod
  apply zle_of_toZ (num 18*U*(num 7*U+num 18))
  have twoGap : 𝔞(monus U two) = 𝔞 U-2 := by
    have eq := natEq (eq_add_of_le h2)
    ipra_simps
    linear_combination -eq
  have nineGap : 𝔞(monus U (num 9)) = 𝔞 U-9 := by
    have eq := natEq (eq_add_of_le h9)
    ipra_simps
    linear_combination -eq
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  rw [twoGap,nineGap]
  ring

/-- The original actual normalized product, with no output-sign premise. -/
theorem product_lower (r s U : PTm n) (hU : Γ ⊢[PRAAx] le (num 18) U)
    (hr : Γ ⊢[PRAAx] RationalNormalForm.wellFormed r) (hs : Γ ⊢[PRAAx] RationalNormalForm.wellFormed s)
    (hhalf : Γ ⊢[PRAAx] upper (fraction one two) r one U)
    (hninth : Γ ⊢[PRAAx] upper (fraction one (num 9)) s one U) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (multiply r s) one U := by
  have h1 : Γ ⊢[PRAAx] le one U := le_trans (le_of_eq_add (d := num 17) (by ipra_ring)) hU
  have h2 : Γ ⊢[PRAAx] le two U := le_trans (le_of_eq_add (d := num 16) (by ipra_ring)) hU
  have h9 : Γ ⊢[PRAAx] le (num 9) U := le_trans (le_of_eq_add (d := num 9) (by ipra_ring)) hU
  have lo := lowered_below two U r h1 hr hhalf
  have hi := lowered_below (num 9) U s h1 hs hninth
  have sign2 := lowered_sign two U (le_succ_self one) h1 h2
  have sign9 := lowered_sign (num 9) U (le_of_eq_add (d := num 8) (by ipra_ring)) h1 h9
  have signr := GaussianRationalL1.nonnegative_of_lower _ _ sign2 lo
  have first := RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _)
    (RationalArithmetic.multiply_monotone (lowered (num 9) U) (lowered two U) r sign9 lo)
  have second := RationalArithmetic.multiply_monotone r (lowered (num 9) U) s signr hi
  exact RationalValueBounds.upper_order_right _ _ _ _ _ (lowered_product_error U hU) (RationalArgmin.transitive first second)

theorem actual_half_ninth_rational_product_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le (num 18) (var 2) ⋏ (RationalNormalForm.wellFormed (var 0) ⋏ RationalNormalForm.wellFormed (var 1))) ⟶
      (upper (fraction one two) (var 0) one (var 2) ⋏ upper (fraction one (num 9)) (var 1) one (var 2)) ⟶
        upper (fraction one (num 18)) (multiply (var 0) (var 1)) one (var 2)) :=
  closeUniv 3 (.impI (.impI (product_lower _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.RationalHalfNinthProductLower
