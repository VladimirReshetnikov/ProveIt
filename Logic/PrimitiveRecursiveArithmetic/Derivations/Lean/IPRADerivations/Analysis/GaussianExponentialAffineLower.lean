import IPRADerivations.Analysis.GaussianPositiveExponentialSeparation
import IPRADerivations.Analysis.GaussianPositiveExponentialTermBound

/-!
# Affine lower bound for the original positive exponential samples

Read the constant and linear coefficients of the actual finite Taylor
sum. At every admitted cutoff the remaining terms are nonnegative.
Consequently the gap from one retains a lower bound for the original
sampled argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianExponentialAffineLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents radius_numerator_norm)
open GaussianPositiveExponentialProduct (scalar_le_add)
open GaussianPositiveExponentialTermBound (positive_suffix)
open GaussianPositiveRealArithmetic (positive positive_add positive_congr natural_representation numerator)
open GaussianRationalExponentialTail (scalarPrefix tail tail_canonical prefix_split)
open GaussianRationalFiniteSum (sum_index_congr)
open GaussianRationalHorner (canonical qadd qmul positive_product represents_congr scalar_congr)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial scalar_sum_zero scalar_sum_succ)
open GaussianRationalReciprocal (power power_succ power_zero)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qadd_commutative)
open RationalArgmin (rationalLE rationalLE_congr transitive denominator_positive)
open RationalSupMetric (denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem inverse_factorial_one : Γ ⊢[PRAAx] inverseFactorial (one : PTm n) ≐ qone := by
  have e : Γ ⊢[PRAAx] Analysis.Products.fact (one : PTm n) ≐ one := by
    have ez := natEq (fact_zero (Γ := Γ) zero)
    have es := natEq (fact_succ (Γ := Γ) zero zero)
    apply deriveNat
    ipra_simps
    linear_combination es + ez
  simpa only [qone,inverseFactorial,GaussianRationalHorner.subst_ofGaussian,
    ComplexLogarithmRemainder.subst_oneCode,Syn.inst_zero,Syn.subst_var] using
    Prf.eqCongr1 (GaussianRationalHorner.ofGaussian ComplexLogarithmRemainder.oneCode (var 0)) e

theorem affine_prefix (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] scalarPrefix q two ≐ qadd qone q := by
  have pow := (power_succ (Γ := Γ) q zero).eqTrans
    ((qmul_congr (power_zero q) (.eqRefl q)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq))
  have linear := (qmul_congr (inverse_factorial_one (Γ := Γ)) pow).eqTrans
    (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq)
  exact (scalar_sum_succ q zero).eqTrans (qadd_congr (scalar_sum_zero q) linear)

theorem finite_gap (q K : PTm n) (hq : Γ ⊢[PRAAx] canonical q) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] qsub (scalarSum q K) qone ≐ qadd q (tail q two (LeanProofs.IPRA.PTm.monus K one)) := by
  let j := LeanProofs.IPRA.PTm.monus K one
  have count : Γ ⊢[PRAAx] succ K ≐ two+j :=
    (congrSucc (eq_add_of_le hK)).eqTrans ((succ_add one j).eqSymm)
  have e := (sum_index_congr scalarBody count (.eqRefl q)).eqTrans (prefix_split q two j)
  have combine : Γ ⊢[PRAAx] qadd (scalarPrefix q two) (tail q two j) ≐ qadd qone (qadd q (tail q two j)) :=
    (qadd_congr (affine_prefix q hq) (.eqRefl (tail q two j))).eqTrans
    (qadd_associative qone q (tail q two j))
  exact (qsub_congr (e.eqTrans combine) (.eqRefl qone)).eqTrans
    (qadd_sub_cancel qone (qadd q (tail q two j)) (GaussianRationalHorner.qadd_canonical _ _))

/-- Transfer a real coordinate lower bound into the existing Gaussian norm
lower-bound judgment for a nonnegative real sample. -/
theorem lower_of_real_order (q A B : PTm n) (hp : Γ ⊢[PRAAx] positive q) (hq : Γ ⊢[PRAAx] canonical q)
    (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint A B)) (fstT q)) : Γ ⊢[PRAAx] lower q A B := by
  let a := fstT q
  let E := denominatorOf a
  let X := numerator a
  have hE : Γ ⊢[PRAAx] le one E := denominator_positive a
  have re := natural_representation a hp.andE₂
  have cmp := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianPositiveExponentialOrder.radius_real_representation A B hB) re hr
  have embed := RationalGaussianEmbedding.embed_from_representation a (ZT.ofNat X) E re
  have actual := (GaussianTranslatedNonconstant.recode_eq q hq).eqSymm.eqTrans
    (RationalGaussianEmbedding.axis_roundtrip q hp.andE₁)
  have rep := represents_congr actual.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _) embed
  apply lower_from_representation q (radiusNumerator X) E A B hE hB rep
  exact le_congr (by ipra_ring)
    ((by ipra_ring : Γ ⊢[PRAAx] X*B*(X*B) ≐ B*B*(X*X)).eqTrans
      (congrMul (.eqRefl _) (radius_numerator_norm X).eqSymm)) (sq_le_sq cmp)

theorem finite_gap_lower (q K A B : PTm n) (hq : Γ ⊢[PRAAx] positive q) (hc : Γ ⊢[PRAAx] canonical q)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint A B)) (fstT q)) :
    Γ ⊢[PRAAx] lower (qsub (scalarSum q K) qone) A B := by
  let j := LeanProofs.IPRA.PTm.monus K one
  let u := tail q two j
  let v := qsub (scalarSum q K) qone
  have hu := positive_suffix q two j hq
  have e := finite_gap q K hc hK
  have hp := positive_congr e.eqSymm (positive_add q u hq hu)
  have ord : Γ ⊢[PRAAx] rationalLE (fstT q) (fstT v) :=
    rationalLE_congr (.eqRefl _) ((congrFst e).eqTrans (RationalGaussianRealPart.real_add q u)).eqSymm
      (scalar_le_add _ _ hc.andE₂.andE₁ hu.andE₂)
  exact lower_of_real_order v A B hp (qsub_canonical _ _) hB (transitive hr ord)

end LeanProofs.IPRA.Analysis.GaussianExponentialAffineLower
