import IPRADerivations.Analysis.GaussianEulerIntegrandName
import IPRADerivations.Analysis.GaussianSignedRealExponentialOrder

/-!
# Order and nonnegative representation for the original Euler decay

The original decay arguments are the signed scalar images of the
positive rational times. The unchanged decay program reverses time
order and has a nonnegative real representative.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayPoint decayData)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData originalData)
open GaussianEuclideanDistanceName (fraction)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianCoefficientNameBounds (unit)
open RationalValueBounds (upper upper_congr)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical ofGaussian_represents represents_congr)
open RationalGaussianEmbedding (embed embed_canonical embed_from_representation native embed_negative)
open RationalIntegerNormalization (normalize_preserves_value)
open RationalArithmetic (negative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedTime (a b : PTm n) : PTm n := negative (fraction a b)

theorem fraction_embedding (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    embed (fraction a b) ≐ GaussianPositiveRationalLogarithm.fraction a b := by
  have value : Γ ⊢[PRAAx] RationalArithmetic.represents (fraction a b) (ZT.ofNat a) b :=
    normalize_preserves_value _ _ hb
  apply canonical_unique _ _ (scale a oneCode) b (embed_canonical _) (ofGaussian_canonical _ _ hb) hb
    (hrv := ofGaussian_represents _ _ hb)
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) (embed_from_representation _ _ _ value)
  apply equal_of_values
  all_goals
    simp only [native,re_scale,im_scale,re_one,im_one,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    try ipra_simps
    ring

theorem signed_time_embedding (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] embed (signedTime a b) ≐ decayPoint a b :=
  (embed_negative (fraction a b)).eqTrans (GaussianInverseBinomialRows.negative_congr (fraction_embedding a b hb))

private theorem subst_exponentialInput {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (exponentialInputData constantF x) = exponentialInputData constantF (Syn.subst σ x) := by
  simp only [exponentialInputData,GaussianRadiusExponentialName.subst_data,GaussianNameBounds.subst_U]

theorem decay_data_eq (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] originalData (signedTime a b) ≐ decayData a b := by
  simpa only [originalData,decayData,subst_exponentialInput,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (exponentialInputData constantF (var 0) : PTm 1)
      (σ := ![embed (signedTime a b)]) (σ' := ![decayPoint a b])
      (fun i => by fin_cases i; exact signed_time_embedding a b hb)

theorem decay_order_at (a b c d p q : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (a*d) (c*b)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 decayF p (decayData c d))) (fstT (ap2 decayF q (decayData a b)))
      (unit p+unit q) (unit p*unit q) := by
  have times := GaussianRationalMetric.comparison_of_cleared (fraction a b) (fraction c d) a c b d hb hd
    (normalize_preserves_value _ _ hb) (normalize_preserves_value _ _ hd) (le_congr (mul_comm a d) (.eqRefl _) h)
  have order : Γ ⊢[PRAAx] realOrder decayF decayF (originalData (signedTime c d)) (originalData (signedTime a b)) :=
    GaussianSignedRealExponentialOrder.original_signed_exponential_order (signedTime c d) (signedTime a b)
      (RationalAlgebra.negative_antitone _ _ times)
  exact upper_congr (congrFst (congrAp2 decayF (.eqRefl p) (decay_data_eq c d hd)))
    (congrFst (congrAp2 decayF (.eqRefl q) (decay_data_eq a b hb))) (.eqRefl _) (.eqRefl _)
    (real_order_at decayF decayF _ _ p q order)

theorem original_decay_order (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (a*d) (c*b)) :
    Γ ⊢[PRAAx] realOrder decayF decayF (decayData c d) (decayData a b) := by
  have bs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift b)) := by
    simpa [Fm.shift,Syn.shift] using hb.shift.shift
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift d)) := by
    simpa [Fm.shift,Syn.shift] using hd.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      le (Syn.shift (Syn.shift a)*Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift c)*Syn.shift (Syn.shift b)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [realOrder,Syn.shift,decayData,subst_exponentialInput,GaussianEulerIntegrandName.subst_decayPoint] using
    decay_order_at (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d))
      (var 1) (var 0) bs ds hs

theorem original_decay_nonnegative_representative (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent positiveF decayF (positiveData (signedTime a b)) (decayData a b) := by
  have bs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift b)) := by
    simpa [Fm.shift,Syn.shift] using hb.shift.shift
  let s := signedTime (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b))
  have e : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent positiveF decayF (positiveData s) (originalData s) :=
    GaussianRealExponentialPositiveRepresentative.original_signed_real_exponential s
  refine .allI (.allI ?_)
  have result := GaussianRationalDistanceOrder.distance_congr (.eqRefl _)
    (congrAp2 decayF (.eqRefl (var 0)) (decay_data_eq _ _ bs)) (.eqRefl _) (.eqRefl _)
    (cross_at positiveF decayF (positiveData s) (originalData s) (var 1) (var 0) e)
  simpa only [crossEquivalent,Syn.shift,decayData,subst_exponentialInput,GaussianEulerIntegrandName.subst_decayPoint,
    GaussianRealExponentialPositiveRepresentative.subst_positiveData,signedTime,RationalArithmetic.subst_negative,
    GaussianEuclideanDistanceName.subst_fraction,s] using result

theorem original_positive_time_decay_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 3)) ⟶ le (var 0*var 3) (var 2*var 1) ⟶
      realOrder decayF decayF (decayData (var 2) (var 3)) (decayData (var 0) (var 1))) :=
  closeUniv 4 (.impI (.impI (original_decay_order _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

theorem original_positive_time_decay_nonnegative_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent positiveF decayF (positiveData (signedTime (var 0) (var 1)))
      (decayData (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_decay_nonnegative_representative _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayOrder
