import IPRADerivations.Analysis.Beta.Tails.ZeroExtension.GaussianBetaZeroExtension
import IPRADerivations.Analysis.Beta.CompactKernels.Regularity.GaussianBetaKernelCompactModulus
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedTime

/-!
# The extended beta sampler at equal rational times

Support depends on the represented time. Two positive rational encodings
at zero distance have identical support. In the supported case use the
old beta modulus at zero input distance, and in the exterior case both
programs give literal zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaZeroExtensionAligned

open_ipra
open GaussianBetaKernelGridComparison (sampleDataBeta)
open GaussianBetaZeroExtension (evaluatorF evaluator_at)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCompactLogarithmBounds (domain original_gaussian_time_distance)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open RationalHarmonicIntervalVariation (gap)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem equal_time_cleared (a b c d : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) zero one) :
    Γ ⊢[PRAAx] a*d ≐ b*c := by
  have raw := original_gaussian_time_distance a b c d zero one hb hd (le_refl one) he
  have g : Γ ⊢[PRAAx] le (gap a b c d) zero :=
    le_congr (one_mul _) (by ipra_ring) raw
  have first := le_trans (le_add_right (Γ := Γ) (monus (a*d) (b*c)) (monus (b*c) (a*d))) g
  have second := le_trans (le_add_left (Γ := Γ) (monus (b*c) (a*d)) (monus (a*d) (b*c))) g
  exact le_antisymm (le_antisymm first (zero_le _)) (le_antisymm second (zero_le _))

theorem support_transfer (a b c d N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (he : Γ ⊢[PRAAx] a*d ≐ b*c) (ha : Γ ⊢[PRAAx] le a (b*N)) :
    Γ ⊢[PRAAx] le c (d*N) :=
  RationalValueBounds.positive_cancel hb
    (le_congr he (by ipra_ring) (mul_le_mul_right d ha))

private theorem raw_at (p t z B N : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (sampleDataBeta z B N) ≐
      RationalArithmetic.select (eqb (monus (fstT t) (sndT t*N)) zero) qzero
        (GaussianBetaKernelGridComparison.row p z B (fstT t) (sndT t) N) := by
  let x := sampleDataBeta z B N
  have degree : Γ ⊢[PRAAx] sndT x ≐ N := snd_pair _ _
  have guard := AnalyticNumberTheory.Euler.congrEqb (congrMonus (.eqRefl (fstT t))
    (congrMul (.eqRefl (sndT t)) degree)) (.eqRefl zero)
  exact (evaluator_at p t x).eqTrans
    (GaussianRationalMonicReconstruction.select_congr guard (.eqRefl _)
      (GaussianBetaKernelCompactModulus.evaluator_raw_at p t z B N))

/-- The comparisons needed for a common grid are at equal values, and
the time pairs themselves may have distinct encodings. -/
theorem aligned_observations (p q t u z R B E N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E)
    (hN : Γ ⊢[PRAAx] le one N)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (fstT t) (sndT t) ⋏ le (sndT t) (E*fstT t))
    (hu : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (fstT u) (sndT u) ⋏ le (sndT u) (E*fstT u))
    (he : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) zero one) :
    Γ ⊢[PRAAx] distanceBounded (ap3 evaluatorF p t (sampleDataBeta z B N))
      (ap3 evaluatorF q u (sampleDataBeta z B N)) (unit p+unit q) (unit p*unit q) := by
  let a := fstT t
  let b := sndT t
  let c := fstT u
  let d := sndT u
  let W := unit p+unit q
  let V := unit p*unit q
  have eq := equal_time_cleared a b c d ht.andE₁.andE₂ hu.andE₁.andE₂ he
  have rev : Γ ⊢[PRAAx] c*b ≐ d*a :=
    (mul_comm _ _).eqTrans (eq.eqSymm.eqTrans (mul_comm _ _))
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (unit_positive p) (unit_positive q)
  refine .orE (GaussianRationalMonicReconstruction.le_or_lt a (b*N)) ?_ ?_
  · have ha : (le a (b*N) :: Γ) ⊢[PRAAx] le a (b*N) := Prf.hyp0
    have hc := support_transfer a b c d N ht.andE₁.andE₂.wk eq.wk ha
    have td : (le a (b*N) :: Γ) ⊢[PRAAx] domain a b E N :=
      .andI ht.andE₁.wk (.andI ht.andE₂.wk (le_congr (.eqRefl _) (mul_comm _ _) ha))
    have ud : (le a (b*N) :: Γ) ⊢[PRAAx] domain c d E N :=
      .andI hu.andE₁.wk (.andI hu.andE₂.wk (le_congr (.eqRefl _) (mul_comm _ _) hc))
    have close := GaussianBetaKernelCompactModulus.row_distance p q z R B E N a b c d N zero one
      (.andI h.wk (.andI td (.andI ud (.andI (le_refl _) he.wk)))) hN.wk (le_refl _)
    have left := (raw_at p t z B N).eqTrans
      (RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.WeightedMangoldt.eqb_one_le ha))
    have right := (raw_at q u z B N).eqTrans
      (RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.WeightedMangoldt.eqb_one_le hc))
    exact distance_congr left.eqSymm right.eqSymm
      (by dsimp only [rateNumerator,W]; ipra_ring) (by dsimp only [rateDenominator,V]; ipra_ring) close
  · have ha : (lt (b*N) a :: Γ) ⊢[PRAAx] lt (b*N) a := Prf.hyp0
    have hc : (lt (b*N) a :: Γ) ⊢[PRAAx] lt (d*N) c :=
      .orE (lt_or_le (d*N) c) Prf.hyp0
        (le_lt_absurd _ (support_transfer c d a b N hu.andE₁.andE₂.wk.wk rev.wk.wk Prf.hyp0) ha.wk)
    have left := (raw_at p t z B N).eqTrans
      (RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.WeightedMangoldt.eqb_zero_lt ha))
    have right := (raw_at q u z B N).eqTrans
      (RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.WeightedMangoldt.eqb_zero_lt hc))
    have near : (lt (b*N) a :: Γ) ⊢[PRAAx] distanceBounded qzero qzero W V :=
      distance_radius_mono _ _ zero V W V hV.wk hV.wk
      (le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _))
      (GaussianRationalPowerDifference.distance_refl_zero qzero V hV.wk)
    exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) near


/-- The original extended evaluator supplies aligned-grid observations
from its native disk and positive degree, including beyond its support. -/
theorem original_aligned_samples (z R B E N C : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianCompactAlignedTime.alignedSamples evaluatorF one C E (sampleDataBeta z B N) := by
  let sh := fun x : PTm n => Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (sh z) (sh R) (sh B) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ,Function.comp_assoc] using h.shift.shift.shift.shift
  have ns : Δ ⊢[PRAAx] le one (sh N) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ,Function.comp_assoc] using hN.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  let t : PTm (n+4) := var 1
  let u : PTm (n+4) := var 0
  let I := GaussianCompactRiemannName.inside one (sh C) (sh E)
  let D := distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) zero one
  let Ξ := D :: I u :: I t :: Δ
  have ht : Ξ ⊢[PRAAx] I t := Prf.hyp1.wk
  have hu : Ξ ⊢[PRAAx] I u := Prf.hyp1
  have hd : Ξ ⊢[PRAAx] D := Prf.hyp0
  have obs := aligned_observations (var 3) (var 2) t u (sh z) (sh R) (sh B) (sh E) (sh N)
    (hs.wk.wk.wk : Ξ ⊢[PRAAx] _) (ns.wk.wk.wk : Ξ ⊢[PRAAx] _)
    (.andI (.andI ht.andE₁ ht.andE₂.andE₁) (le_congr (one_mul _) (.eqRefl _) ht.andE₂.andE₂.andE₁))
    (.andI (.andI hu.andE₁ hu.andE₂.andE₁) (le_congr (one_mul _) (.eqRefl _) hu.andE₂.andE₂.andE₁))
    hd
  simpa only [GaussianCompactAlignedTime.body,GaussianBetaKernelGridComparison.subst_sampleDataBeta,
    Syn.shift,sh,Δ,Ξ,D,I,t,u,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using obs

theorem actual_extended_beta_equal_time_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((GaussianEulerExponentCompactBounds.source (var 0) (var 1) (var 2) (var 3) ⋏ le one (var 4)) ⟶
      GaussianCompactAlignedTime.alignedSamples evaluatorF one (var 5) (var 3)
        (sampleDataBeta (var 0) (var 2) (var 4))) :=
  closeUniv 6 (.impI (original_aligned_samples _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaZeroExtensionAligned
