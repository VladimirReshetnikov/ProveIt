import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayIncrement
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannName
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling
import IPRADerivations.Core.CongruenceTactic

/-!
# Finite telescoping for the original Euler decay

For the uniform mesh at (a+i)/B, the weighted left sum of the
actual decay observations differs from the endpoint difference by
at most 3N/B²+20N·2⁻ᵖ. The endpoint order and summation are
expressed in the same canonical Gaussian rational codes as the sampler.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianEulerDecayIncrement (decay_linear_increment)
open GaussianGammaCanonicalExponent (constantF)
open GaussianRationalHorner (qadd qmul qmul_canonical qzero positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qone qone_canonical)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalFiniteSum (sum)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameRingLaws (three)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observation (a b p : PTm n) : PTm n := ap2 decayF p (decayData a b)
def gridData (a b p : PTm n) : PTm n := pairT a (pairT b p)
def sample (i x : PTm n) : PTm n := observation (fstT x+i) (fstT (sndT x)) (sndT (sndT x))
def weightedBody : PTm 2 := qmul (sample (var 0) (var 1)) (fraction one (fstT (sndT (var 1))))
def differenceBody : PTm 2 := qsub (sample (var 0) (var 1)) (sample (succ (var 0)) (var 1))
def stepError (b c p : PTm n) : PTm n := three*c*c*unit p+num 20*(b*b)
def errorNum (b p : PTm n) : PTm n := three*unit p+num 20*(b*b)
def errorDen (b p : PTm n) : PTm n := b*b*unit p

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (a b p : PTm n) :
    Syn.subst σ (observation a b p) = observation (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) := by
  simp [observation,decayData,GaussianGammaFiniteApproximantName.exponentialInputData]
@[simp] theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (a b p : PTm n) :
    Syn.subst σ (gridData a b p) = gridData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) := by simp [gridData]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (i x : PTm n) :
    Syn.subst σ (sample i x) = sample (Syn.subst σ i) (Syn.subst σ x) := by simp [sample]

theorem read_grid (a b p i : PTm n) : Γ ⊢[PRAAx]
    sample i (gridData a b p) ≐ observation (a+i) b p := by
  let v := pairT b p
  let x := gridData a b p
  have front : Γ ⊢[PRAAx] fstT x+i ≐ a+i := congrAdd (fst_pair a v) (.eqRefl i)
  have middle : Γ ⊢[PRAAx] fstT (sndT x) ≐ b := (congrFst (snd_pair a v)).eqTrans (fst_pair b p)
  have last : Γ ⊢[PRAAx] sndT (sndT x) ≐ p := (congrSnd (snd_pair a v)).eqTrans (snd_pair b p)
  ipra_congr (observation (var 0) (var 1) (var 2) : PTm 3) with [front, middle, last] using [sample, x]

private theorem obs_point_congr (a b c d p : PTm n) (h : Γ ⊢[PRAAx] decayPoint a b ≐ decayPoint c d) :
    Γ ⊢[PRAAx] observation a b p ≐ observation c d p := by
  ipra_congr (ap2 decayF (var 0) (GaussianRadiusExponentialName.data (GaussianNameBounds.U constantF (var 1)) (var 1)) : PTm 2) with
    [.eqRefl p, h] using [observation, decayData, GaussianGammaFiniteApproximantName.exponentialInputData]

theorem observation_numerator_congr (a c b p : PTm n) (e : Γ ⊢[PRAAx] a ≐ c) :
    Γ ⊢[PRAAx] observation a b p ≐ observation c b p :=
  obs_point_congr _ _ _ _ _ (GaussianInverseBinomialRows.negative_congr
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ e (.eqRefl b)))

theorem observation_rescale (a b k p : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] observation (a*k) (b*k) p ≐ observation a b p := by
  have h : Γ ⊢[PRAAx] equal (scale (a*k) oneCode) (scale k (scale a oneCode)) := by
    apply equal_of_values
    all_goals simp only [re_scale,im_scale,re_one,im_one]; ipra_simps; ring
  have hf := positive_product b k hb hk
  have e := (GaussianGammaFiniteValueProperness.fraction_equal _ _ (b*k) hf h).eqTrans
    ((GaussianGammaEncodingRescaling.fraction_denominator_congr _ _ _ (mul_comm b k)).eqTrans
      (GaussianGammaEncodingRescaling.fraction_rescale (scale a oneCode) b k hb hk))
  exact obs_point_congr _ _ _ _ _ (GaussianInverseBinomialRows.negative_congr e)

private theorem observation_step (a b c p : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] observation (a*b+c*b) (b*b) p ≐ observation (a+c) b p :=
  (observation_numerator_congr _ _ (b*b) p (by ipra_ring)).eqTrans (observation_rescale (a+c) b b p hb hb)

private theorem translating_step (X Y h D E : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hX : Γ ⊢[PRAAx] GaussianRationalHorner.canonical X)
    (hNear : Γ ⊢[PRAAx] distanceBounded Y (qmul X (qsub qone h)) E D) :
    Γ ⊢[PRAAx] distanceBounded (qmul X h) (qsub X Y) E D := by
  let W := qmul X h
  let S := qsub qone h
  have e : Γ ⊢[PRAAx] qadd (qmul X S) W ≐ X := by
    refine (GaussianRationalCoefficientScaling.qmul_add X S h).eqSymm.eqTrans ?_
    exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl X)
      ((GaussianReciprocalHorner.qadd_commutative S h).eqTrans (GaussianRationalLinearProduct.add_sub_right h qone qone_canonical))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right X hX)
  have same := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD hNear
    (GaussianRationalPowerDifference.distance_refl_zero W D hD)
  have same' := distance_congr (.eqRefl _) e (add_zero E) (.eqRefl _) same
  have added := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD same'
    (GaussianRationalPowerDifference.distance_refl_zero (qnegative Y) D hD)
  exact distance_congr (GaussianRationalSyntheticDivision.qadd_sub_cancel Y W (qmul_canonical X h))
    (.eqRefl _) (add_zero E) (.eqRefl _) added

theorem adjacent_step (a b c p : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hcb : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] distanceBounded (qmul (observation a b p) (fraction c b))
      (qsub (observation a b p) (observation (a+c) b p)) (stepError b c p) (errorDen b p) := by
  have hx : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (observation a b p) :=
    GaussianRadiusExponentialName.sample_canonical constantF _ p (decayPoint a b)
  have remainder := decay_linear_increment a b c b p ha hb hc hb hcb
  refine translating_step _ _ _ _ _ (positive_product _ _ (positive_product b b hb hb) (unit_positive p)) hx ?_
  exact distance_congr (observation_step a b c p hb) (.eqRefl _) (.eqRefl _) (.eqRefl _) remainder

theorem grid_step (a b p i : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (inst2 weightedBody i (gridData a b p))
      (inst2 differenceBody i (gridData a b p)) (errorNum b p) (errorDen b p) := by
  let X := observation (a+i) b p
  let Y := observation (a+succ i) b p
  let h := fraction one b
  let x := gridData a b p
  have y : Γ ⊢[PRAAx] observation (a+i+one) b p ≐ Y :=
    observation_numerator_congr _ _ b p (by ipra_ring)
  have distance : Γ ⊢[PRAAx] distanceBounded (qmul X h) (qsub X Y) (errorNum b p) (errorDen b p) :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl X) y)
      (by dsimp only [stepError,errorNum]; ipra_ring) (.eqRefl _)
      (adjacent_step (a+i) b one p (le_trans ha (le_add_right a i)) hb (le_refl one) hb)
  have den : Γ ⊢[PRAAx] fstT (sndT x) ≐ b := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have w : Γ ⊢[PRAAx] inst2 weightedBody i x ≐ qmul X h := by
    simpa [weightedBody,inst2,fraction,x,X,h] using GaussianRationalSyntheticDivision.qmul_congr (read_grid a b p i)
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl one) den)
  have v : Γ ⊢[PRAAx] inst2 differenceBody i x ≐ qsub X Y := by
    simpa [differenceBody,inst2] using GaussianRationalSyntheticDivision.qsub_congr
      (read_grid a b p i) (read_grid a b p (succ i))
  exact distance_congr w.eqSymm v.eqSymm (.eqRefl _) (.eqRefl _) distance

def telescopeLaw (x k : PTm n) : Fm PTm n :=
  sum differenceBody k x ≐ qsub (sample zero x) (sample k x)
@[simp] theorem subst_telescopeLaw {m : ℕ} (σ : Fin n → PTm m) (x k : PTm n) :
    (telescopeLaw x k).subst σ = telescopeLaw (Syn.subst σ x) (Syn.subst σ k) := by simp [telescopeLaw]

def consecutiveDifference (f : PTm 2) : PTm 2 :=
  qsub (inst2 f (var 0) (var 1)) (inst2 f (succ (var 0)) (var 1))

@[simp] theorem consecutive_difference_at (f : PTm 2) (i x : PTm n) :
    inst2 (consecutiveDifference f) i x = qsub (inst2 f i x) (inst2 f (succ i) x) := by
  change Syn.subst ![i,x] (consecutiveDifference f) = _
  simp [consecutiveDifference]

private def differenceSumLaw (f : PTm 2) (x k : PTm n) : Fm PTm n :=
  sum (consecutiveDifference f) k x ≐ qsub (inst2 f zero x) (inst2 f k x)

@[simp] private theorem subst_differenceSumLaw {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x k : PTm n) :
    (differenceSumLaw f x k).subst σ = differenceSumLaw f (Syn.subst σ x) (Syn.subst σ k) := by
  simp [differenceSumLaw]

theorem consecutive_difference_sum (f : PTm 2) (x k : PTm n) :
    Γ ⊢[PRAAx] sum (consecutiveDifference f) k x ≐ qsub (inst2 f zero x) (inst2 f k x) := by
  have all : Γ ⊢[PRAAx] .all (differenceSumLaw f (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_differenceSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self _).eqSymm
    · simp only [subst_differenceSumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine (GaussianRationalFiniteSum.sum_succ (consecutiveDifference f) _ _).eqTrans ?_
      rw [consecutive_difference_at]
      exact (qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans
        (GaussianReconstructionRoots.difference_chain (inst2 f zero (Syn.shift x))
          (inst2 f (var 0) (Syn.shift x)) (inst2 f (succ (var 0)) (Syn.shift x)))
  have done : Γ ⊢[PRAAx] differenceSumLaw f x k := by
    simpa only [subst_differenceSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact done

theorem telescope (x k : PTm n) : Γ ⊢[PRAAx] telescopeLaw x k := by
  have body : consecutiveDifference (sample (var 0) (var 1) : PTm 2) = differenceBody := by
    simp [consecutiveDifference,differenceBody,inst2]
  simpa [body,telescopeLaw,inst2] using consecutive_difference_sum (sample (var 0) (var 1)) x k

theorem actual_decay_mesh (a b p N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (sum weightedBody N (gridData a b p))
      (qsub (sample zero (gridData a b p)) (sample N (gridData a b p))) (N*errorNum b p) (errorDen b p) := by
  let x := gridData a b p
  have hD : Γ ⊢[PRAAx] le one (errorDen b p) :=
    positive_product _ _ (positive_product b b hb hb) (unit_positive p)
  have terms : Γ ⊢[PRAAx] termsDistance weightedBody differenceBody N x x (errorNum b p) (errorDen b p) := by
    have ha' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
    have hb' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
    refine .allI (.impI ?_)
    simpa [x,termsDistance,Syn.shift,errorNum,errorDen,three] using
      (grid_step (Syn.shift a) (Syn.shift b) (Syn.shift p) (var 0) ha'.wk hb'.wk)
  exact distance_congr (.eqRefl _) (telescope x N) (.eqRefl _) (.eqRefl _)
    (sum_distance weightedBody differenceBody N x x (errorNum b p) (errorDen b p) hD terms)

theorem original_Euler_decay_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 1) ⟶
      distanceBounded (sum weightedBody (var 3) (gridData (var 0) (var 1) (var 2)))
        (qsub (sample zero (gridData (var 0) (var 1) (var 2))) (sample (var 3) (gridData (var 0) (var 1) (var 2))))
        (var 3*errorNum (var 1) (var 2)) (errorDen (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (actual_decay_mesh _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayMesh
