import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.Apartness.GaussianGammaNegativeIntervalInverseRationalEnvelope
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalCorrectionSlope
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSqrtBrackets
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFubini

/-!
# Uniform variation of the inverse Gamma shift derivative

The reciprocal sum changes by at most the displacement times its
term count and the square of the inverse pole margin. The inverse
shift multiplier has its own uniform variation bound. Their product
gives the Lipschitz bound for the actual derivative coefficient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCorrectionVariation

open_ipra
open GaussianEulerExponentCompactBounds (fraction_bound)
open GaussianEulerUnitCompactTimeBounds (gap_margin)
open GaussianGammaNegativeCriticalCorrection (guard correction body bottomDen den_expand positiveSum row row_at row_den_positive)
open GaussianGammaNegativeCriticalCorrectionSlope (correction_distance)
open GaussianGammaNegativeIntervalInverseRationalEnvelope (window inverse_bound_on_window window_envelope)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse correctionFactor)
open GaussianGammaNegativeIntervalRescale (guard_rescale)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (bounded_sum_same product_difference)
open GaussianRationalReciprocal (bound_congr bounded_difference bounded_product bounded_product_one)
open GaussianRationalRiemannRefinement (sum_distance)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianStirlingRationalTelescopers (fraction_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def correctionCap (E N : PTm n) : PTm n := succ (succ N)*E
def correctionGain (E N : PTm n) : PTm n := succ (succ N)*(E*E)
def gain (E N : PTm n) : PTm n :=
  inverseGapCost (succ N) (E*E)*correctionCap E N+(E*E)*correctionGain E N

ipra_subst correctionCap

ipra_subst correctionGain

ipra_subst gain

private theorem denominator_positive {a b : PTm n} (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx] le one b :=
  le_trans h.andE₁ (le_of_lt h.andE₂)

private theorem row_bound (a b E j : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] bounded (row a b j) E one := by
  have e := natEq (den_expand a b j h.andE₁.andE₂)
  have cap := gap_margin a b E h
  exact fraction_bound b (bottomDen a b j) E (row_den_positive a b j h.andE₁.andE₂)
    (by ipra_le sl cap+𝔞(E)*𝔞(j)*𝔞(b) with 𝔞(E)*e)

set_option maxHeartbeats 700000 in
private theorem sum_bound (a b E L : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] bounded (positiveSum a b L) (L*E) one := by
  have terms : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.termsDistance body (qzero : PTm 2) L (pairT a b) (pairT a b) E one := by
    refine .allI (.impI ?_)
    let A := Syn.shift a
    let B := Syn.shift b
    let K := Syn.shift E
    let J : PTm (n+1) := var 0
    let Δ := lt J (Syn.shift L) :: Γ.map Fm.shift
    have w : Γ.map Fm.shift ⊢[PRAAx] window A B K := by simpa [Fm.shift,Syn.shift,A,B,K] using h.shift
    have r : Δ ⊢[PRAAx] distanceBounded (row A B J) qzero K one :=
      (distance_zero_iff (row A B J) K one (le_refl one)).iffMpr (row_bound A B K J w.wk)
    simpa only [Syn.shift, subst_pairT, A, B, K, J, Δ, inst2, GaussianRationalHorner.subst_qzero,
      one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
      distance_congr (row_at A B J).eqSymm (.eqRefl qzero) (.eqRefl _) (.eqRefl _) r
  exact (distance_zero_iff (positiveSum a b L) (L*E) one (le_refl one)).iffMp
    (distance_congr (.eqRefl _) (GaussianRationalFubini.zero_body_sum L (pairT a b)) (.eqRefl _) (.eqRefl _)
      (sum_distance body (qzero : PTm 2) L (pairT a b) (pairT a b) E one (le_refl one) terms))

theorem correction_bound (a b E N : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] bounded (correction a b N) (correctionCap E N) one :=
  bound_congr (.eqRefl _) (by unfold correctionCap; ipra_ring) (by ipra_ring)
    (bounded_difference _ _ (succ N*E) one E one (le_refl one) (le_refl one)
      (sum_bound a b E (succ N) h) (fraction_bound b a E h.andE₁.andE₁ h.andE₂.andE₂.andE₁))

theorem factor_bound (a b E N : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] bounded (correctionFactor a b N) ((E*E)*correctionCap E N) one :=
  bounded_product_one (inverse_bound_on_window a b E N h) (correction_bound a b E N h)

private theorem gap_budget (a c b A D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (hac : Γ ⊢[PRAAx] le a c) (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) :
    Γ ⊢[PRAAx] le (D*monus c a) (A*b) := by
  have h := (GaussianGammaHalfSqrtBrackets.fraction_gap c b a b A D hb hb hD hStep).andE₁
  have e := natEq (eq_add_of_le hac)
  have hc : Γ ⊢[PRAAx] le (b*(D*monus c a)+D*(a*b)) (b*(A*b)+D*(a*b)) :=
    le_congr (by apply deriveNat; ipra_simps; linear_combination 𝔞(D)*𝔞(b)*e) (by ipra_ring) h
  exact RationalValueBounds.positive_cancel hb (le_of_add_le_add_right hc)

private theorem ordered_correction_variation (a c b E N A D : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c b E) (hac : Γ ⊢[PRAAx] le a c)
    (hD : Γ ⊢[PRAAx] le one D) (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) :
    Γ ⊢[PRAAx] distanceBounded (correction c b N) (correction a b N) (correctionGain E N*A) D := by
  have hb := denominator_positive ha.andE₁
  have raw := correction_distance a c b N E
    (.andI (.andI ha.andE₁.andE₁ (.andI hac hc.andE₁.andE₂)) (.andI ha.andE₂.andE₂.andE₁ (gap_margin c b E hc)))
  have cap := gap_budget a c b A D hb hD hac hStep
  exact distance_radius_mono _ _ _ _ _ _ hb hD
    (by unfold GaussianGammaNegativeCriticalCorrectionSlope.budget GaussianGammaNegativeCriticalCorrectionSlope.rowBudget correctionGain
        ipra_le 𝔞(succ (succ N))*𝔞(E)^2*sl cap) raw

private theorem common_correction_variation (a c b E N A D : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c b E) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c b) A D) :
    Γ ⊢[PRAAx] distanceBounded (correction a b N) (correction c b N) (correctionGain E N*A) D :=
  .orE (le_total c a) (ordered_correction_variation c a b E N A D hc.wk ha.wk Prf.hyp0 hD.wk hStep.wk)
    (distance_symmetric _ _ _ _ hD.wk (ordered_correction_variation a c b E N A D ha.wk hc.wk Prf.hyp0 hD.wk
      (distance_symmetric _ _ _ _ hD.wk hStep.wk)))

private theorem rescaled_window (a b E s : PTm n) (h : Γ ⊢[PRAAx] window a b E) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] window (s*a) (s*b) E :=
  .andI (guard_rescale a b s h.andE₁ hs) (.andI h.andE₂.andE₁ (.andI
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right s h.andE₂.andE₂.andE₁))
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right s h.andE₂.andE₂.andE₂))))

private theorem window_den_congr {a b d E : PTm n} (e : Γ ⊢[PRAAx] b ≐ d) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] window a d E := by
  simpa using Prf.eqSubst (window (var 0) (var 1) (var 2) : Fm PTm 3) ![a,b,E] ![a,d,E]
    (fun k => by fin_cases k; exact .eqRefl a; exact e; exact .eqRefl E) (by simpa using h)

private theorem correction_den_congr {a b d N : PTm n} (e : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] correction a b N ≐ correction a d N := by
  simpa using Prf.eqCongr (correction (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a,d,N])
    (fun k => by fin_cases k; exact .eqRefl a; exact e; exact .eqRefl N)

theorem correction_variation (a b c d E N A D : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c d E) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) :
    Γ ⊢[PRAAx] distanceBounded (correction a b N) (correction c d N) (correctionGain E N*A) D := by
  have hb := denominator_positive ha.andE₁
  have hd := denominator_positive hc.andE₁
  have hB := positive_product (Γ := Γ) _ _ hd hb
  have ha' := rescaled_window a b E d ha hd
  have hc' := window_den_congr (mul_comm b d) (rescaled_window c d E b hc hb)
  have left := fraction_same (d*a) (d*b) a b hB hb (by ipra_ring)
  have right := fraction_same (b*c) (d*b) c d hB hd (by ipra_ring)
  have rate := common_correction_variation (d*a) (b*c) (d*b) E N A D ha' hc' hD
    (distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) hStep)
  exact distance_congr (GaussianGammaNegativeCriticalRescale.correction_rescale a b N d ha.andE₁ hd)
    ((correction_den_congr (mul_comm d b)).eqTrans (GaussianGammaNegativeCriticalRescale.correction_rescale c d N b hc.andE₁ hb))
    (.eqRefl _) (.eqRefl _) rate

theorem rational_variation (a b c d E N A D : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c d E) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) :
    Γ ⊢[PRAAx] distanceBounded (correctionFactor a b N) (correctionFactor c d N) (gain E N*A) D := by
  let i := inverse a b N
  let j := inverse c d N
  let u := correction a b N
  let v := correction c d N
  let H := E*E
  let V := inverseGapCost (succ N) H*A
  let P := correctionCap E N
  let R := correctionGain E N*A
  have first := (window_envelope c d a b E N A D hc ha hD hStep).andE₁
  have second := correction_variation a b c d E N A D ha hc hD hStep
  have uBound : Γ ⊢[PRAAx] bounded (qmul (GaussianRationalMetric.qsub i j) u) (V*P) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ V D P one hD (le_refl one) first (correction_bound a b E N ha))
  have vBound : Γ ⊢[PRAAx] bounded (qmul j (GaussianRationalMetric.qsub u v)) (H*R) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ H one R D (le_refl one) hD (inverse_bound_on_window c d E N hc) second)
  exact bound_congr (product_difference i j u v).eqSymm
    (by unfold V P H R gain; ipra_ring) (.eqRefl _) (bounded_sum_same _ _ _ _ _ hD uBound vBound)

theorem actual_negative_Gamma_correction_factor_rational_variation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (window (var 0) (var 1) (var 4) ⟶ window (var 2) (var 3) (var 4) ⟶ le one (var 7) ⟶
        distanceBounded (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (var 6) (var 7) ⟶
          distanceBounded (correctionFactor (var 0) (var 1) (var 5)) (correctionFactor (var 2) (var 3) (var 5))
            (gain (var 4) (var 5)*var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI
    (rational_variation _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCorrectionVariation
