import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineRootNormalization
import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSincRatio

/-!
# Finite transport from a multiplied sine identity to a quotient row

Compare the cross-products before reciprocation. Only the two
denominators actually present in the normalized factors require
lower bounds. This also covers a zero numerator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductQuotientTransport

open_ipra
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (qone reciprocal bounded_product bound_congr)
open GaussianRationalLowerBounds (lower product_lower lower_congr reciprocal_identity_of_lower inverse_bound)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianNamedDifference (difference_distance)
open GaussianNameArithmetic (product_distance)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianSineRootNormalization (normalizedFactor)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def correctedFactor (b s t : PTm n) : PTm n :=
  qsub qone (qmul (qmul b b) (qmul (reciprocal (qmul t t)) (qmul s s)))

ipra_subst correctedFactor

private theorem inverse_identity (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] lower a one D) : Γ ⊢[PRAAx] qmul (reciprocal a) a ≐ qone :=
  (qmul_commutative _ _).eqTrans
    (reciprocal_identity_of_lower a one D (le_refl one) hD h)

theorem cross_quotient_bound (u v a b E M V B : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hV : Γ ⊢[PRAAx] le one V) (hB : Γ ⊢[PRAAx] le one B)
    (hv : Γ ⊢[PRAAx] lower v one V) (hb : Γ ⊢[PRAAx] lower b one B)
    (h : Γ ⊢[PRAAx] distanceBounded (qmul u b) (qmul v a) E M) :
    Γ ⊢[PRAAx] distanceBounded (qmul u (reciprocal v)) (qmul (reciprocal b) a) ((V*B)*E) M := by
  let P := qmul (reciprocal v) (reciprocal b)
  have bound : Γ ⊢[PRAAx] bounded P (V*B) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
        (inverse_bound v one V (le_refl one) hV hv) (inverse_bound b one B (le_refl one) hB hb))
  have left : Γ ⊢[PRAAx] qmul P (qmul u b) ≐ qmul u (reciprocal v) :=
    (qmul_shuffle _ _ _ _).eqTrans
      ((qmul_congr (.eqRefl _) (inverse_identity b B hB hb)).eqTrans
        ((qmul_one_right _ (qmul_canonical _ _)).eqTrans (qmul_commutative _ _)))
  have right : Γ ⊢[PRAAx] qmul P (qmul v a) ≐ qmul (reciprocal b) a :=
    (qmul_shuffle _ _ _ _).eqTrans
      ((qmul_congr (inverse_identity v V hV hv) (.eqRefl _)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (qmul_canonical _ _)))
  exact distance_congr left right (.eqRefl _) (.eqRefl _)
    (multiply_distance P _ _ (V*B) E M hM bound h)

theorem corrected_factor_error (u v b s t E M W V : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hV : Γ ⊢[PRAAx] le one V)
    (hv : Γ ⊢[PRAAx] lower v one V)
    (ht : Γ ⊢[PRAAx] lower (qmul t t) one (num 4))
    (hL : Γ ⊢[PRAAx] bounded (qmul u t) W one)
    (hR : Γ ⊢[PRAAx] bounded (qmul v (qmul b s)) W one)
    (h : Γ ⊢[PRAAx] distanceBounded (qmul u t) (qmul v (qmul b s)) E M) :
    Γ ⊢[PRAAx] distanceBounded (normalizedFactor u v) (correctedFactor b s t)
      (((V*V)*num 4)*(two*W*E)) M := by
  let L := qmul u t
  let R := qmul v (qmul b s)
  let A := qmul u u
  let B := qmul v v
  let C := qmul (qmul b b) (qmul s s)
  let D := qmul t t
  have eR : Γ ⊢[PRAAx] qmul R R ≐ qmul B C :=
    (qmul_shuffle _ _ _ _).eqTrans (qmul_congr (.eqRefl _) (qmul_shuffle _ _ _ _))
  have d : Γ ⊢[PRAAx] distanceBounded (qmul A D) (qmul B C) (two*W*E) M :=
    distance_congr (qmul_shuffle _ _ _ _) eR (by ipra_ring) (.eqRefl _)
      (product_distance L R L R E E M W W hM h h hL hR)
  have vSq : Γ ⊢[PRAAx] lower B one (V*V) := lower_congr (.eqRefl _) (one_mul one) (.eqRefl _)
    (product_lower _ _ one V one V hV hV hv hv)
  have twice : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have dist := cross_quotient_bound A B C D (two*W*E) M (V*V) (num 4) hM
    (positive_product _ _ hV hV) twice vSq ht d
  have toRight : Γ ⊢[PRAAx] qmul (reciprocal D) C ≐ qmul (qmul b b) (qmul (reciprocal D) (qmul s s)) :=
    (qmul_commutative _ _).eqTrans
      (by
        refine (qmul_associative _ _ _).eqTrans ?_
        exact qmul_congr (.eqRefl _) (qmul_commutative _ _))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (difference_distance qone qone _ _ zero _ _ hM (distance_refl_zero qone M hM)
      (distance_congr (.eqRefl _) toRight (.eqRefl _) (.eqRefl _) dist))

end LeanProofs.IPRA.Analysis.GaussianSineProductQuotientTransport
