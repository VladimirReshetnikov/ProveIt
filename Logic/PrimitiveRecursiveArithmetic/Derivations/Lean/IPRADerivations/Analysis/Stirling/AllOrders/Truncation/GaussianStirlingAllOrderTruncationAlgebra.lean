import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.GaussianStirlingAllOrderTruncationCoefficients
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# Exact observation algebra for logarithmic truncation

The signed reciprocal degree changes the positive centered-kernel
recurrence into subtraction of one literal logarithmic term.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationAlgebra

open_ipra
open GaussianStirlingAllOrderPanelPartsNames (initial derivativeRatio weightedPrimitive)
open GaussianStirlingAllOrderTruncationCoefficients (scaleCode scale_ratio sign literalTerm scale_mean_primitive)
open GaussianRationalHorner (qadd qmul qzero canonical represents_congr canonical_unique positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical qsub_canonical qsub_represents qnegative_represents)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRootAlgebra (equal_of_values re_sub im_sub re_neg im_neg)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalIntegerNormalization (normalize_preserves_value)
open RationalGaussianEmbedding (embed embed_multiply embed_negative embed_one)
open RationalGaussianRealPart (embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedScale (m : ℕ) : PTm n := embed (scaleCode m)
def correction (m : ℕ) (A B : PTm n) : PTm n := embed (literalTerm m A B)
def truncation : ℕ → PTm n → PTm n → PTm n
  | 0,_,_ => qzero
  | m+1,A,B => qadd (truncation m A B) (correction m A B)

@[simp] theorem subst_signedScale {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (signedScale m : PTm n) = (signedScale m : PTm l) := by simp [signedScale]
ipra_subst correction
@[simp] theorem subst_truncation {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (truncation m A B) = truncation m (Syn.subst σ A) (Syn.subst σ B) := by
  induction m with
  | zero => simp [truncation]
  | succ m ih => simp [truncation,ih]

private theorem negative_sub_flip (a b : PTm n) : Γ ⊢[PRAAx] qnegative (qsub a b) ≐ qsub b a := by
  let A := rawGaussian a
  let B := rawGaussian b
  let D := rawDen a*rawDen b
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (raw_den_positive a) (raw_den_positive b)
  have ha := GaussianRationalSyntheticDivision.rescale_to a A (rawDen a) (rawDen b) D
    (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hb := GaussianRationalSyntheticDivision.rescale_to b B (rawDen b) (rawDen a) D
    (raw_represents (Γ := Γ) b) (mul_comm _ _)
  have hl := qnegative_represents _ _ _ (qsub_represents _ _ _ _ D hd ha hb)
  have hr := qsub_represents _ _ _ _ D hd hb ha
  apply canonical_unique _ _ _ _ (qnegative_canonical _) (qsub_canonical _ _) hd (hrv := hr)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := hl)
  apply equal_of_values <;> simp only [re_neg,im_neg,re_sub,im_sub] <;> ring

theorem signed_initial_cancel : Γ ⊢[PRAAx]
    qmul (signedScale 0 : PTm n) initial ≐ GaussianRationalSyntheticDivision.qone := by
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have v : Γ ⊢[PRAAx] scaleCode (n := n) 0 ≐ fraction one two := by
    have h : Γ ⊢[PRAAx] le one (LeanProofs.IPRA.PTm.num 2 : PTm n) := by ipra_le 1
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ h) (RationalNormalForm.normalize_well_formed _ _ h₂)
      (normalize_preserves_value _ _ h) (fraction_represents _ _ h₂) h h₂
    apply ZT.derive
    have e := natEq (show Γ ⊢[PRAAx] (LeanProofs.IPRA.PTm.num 2 : PTm n) ≐ two by ipra_ring)
    simp only [BernoulliBounds.toZ_zint,sign,pow_zero,Int.cast_one,ZT.toZ_mul,ZT.toZ_ofNat]
    rw [e]
    ipra_simps <;> ring
  have p : Γ ⊢[PRAAx] RationalArithmetic.multiply (fraction one two : PTm n) (fraction two one) ≐ fraction one one := by
    have h := positive_product _ _ h₂ (le_refl one)
    refine (RationalNonnegativePowers.fraction_multiply one two two one h₂ (le_refl one)).eqTrans ?_
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ h) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      (fraction_represents _ _ h) (fraction_represents _ _ (le_refl one)) h (le_refl one)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact (qmul_congr (embed_congr v) (.eqRefl _)).eqTrans
    ((embed_multiply _ _).eqSymm.eqTrans ((embed_congr p).eqTrans embed_one))

theorem signed_recurrence_exact (m : ℕ) (A B J : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    qmul (signedScale (m+1)) (qmul (derivativeRatio m) (qsub (weightedPrimitive m A B) J)) ≐
      qsub (qmul (signedScale m) J) (correction m A B) := by
  let s := signedScale (n := n) m
  let p := weightedPrimitive m A B
  have ratioLaw : Γ ⊢[PRAAx] qmul (signedScale (m+1)) (derivativeRatio m) ≐ qnegative s :=
    (embed_multiply _ _).eqSymm.eqTrans ((embed_congr (scale_ratio m)).eqTrans (embed_negative _))
  have primitiveLaw : Γ ⊢[PRAAx] qmul s p ≐ correction m A B :=
    (embed_multiply _ _).eqSymm.eqTrans (embed_congr (scale_mean_primitive m A B hA))
  exact (qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr ratioLaw (.eqRefl _)).eqTrans
      ((GaussianInverseBinomialRows.negative_product s (qsub p J)).eqSymm.eqTrans
        ((RationalGaussianEmbedding.negative_congr (GaussianRationalRoundedPower.multiplication_difference s p J).eqSymm).eqTrans
          ((negative_sub_flip (qmul s p) (qmul s J)).eqTrans (qsub_congr (.eqRefl _) primitiveLaw)))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationAlgebra
