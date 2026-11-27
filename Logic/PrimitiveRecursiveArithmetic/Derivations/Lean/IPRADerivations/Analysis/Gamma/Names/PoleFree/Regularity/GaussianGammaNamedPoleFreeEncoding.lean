import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaNamedPoleFreeModulus
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale

/-!
# Raw representation invariance of the pole-free Gamma source

Disk and pole certificates are inequalities about rational values.
They therefore hold for the actual raw Gaussian numerator and common
denominator of a named sample, as well as for its original encoding.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeEncoding

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard pole_at)
open GaussianGammaHalfPlaneInputContinuity (modulus)
open GaussianGammaReciprocalInverse (source gammaF gammaData gamma_regular)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_radius_mono_same)
open GaussianRationalHorner (qadd represents represents_congr represents_rescale positive_product
  ofGaussian ofGaussian_represents ofGaussian_canonical qadd_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (bounded distanceBounded bounded_iff)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem translated_represents (q z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q z B) : Γ ⊢[PRAAx]
    represents (qadd q (naturalPoint k)) (translated z B k) B := by
  have e : Γ ⊢[PRAAx] equal (scale B (scale k oneCode)) (scale (B*k) oneCode) := by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one,Q.mk_mul,map_mul] <;> ring
  have p := represents_rescale (naturalPoint k) (scale k oneCode) one B (natural_point_represents (Γ := Γ) k)
  exact qadd_represents _ _ _ _ _ hB hq (represents_congr (.eqRefl _) e (one_mul B) p)

private theorem raw_pole_at (q z R B A E k : PTm n) (hz : Γ ⊢[PRAAx] source z R B A E)
    (hq : Γ ⊢[PRAAx] represents q z B) (hk : Γ ⊢[PRAAx] le k (two*R)) : Γ ⊢[PRAAx]
    poleAt (rawGaussian q) (rawDen q) A E k := by
  let v := qadd q (naturalPoint k)
  have hb := hz.andE₁.andE₂.andE₁
  have he := hz.andE₂.andE₂.andE₁
  have base := pole_at z B A E (two*R) k hz.andE₂.andE₂.andE₂ hk
  have n : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower v A E :=
    GaussianRationalLowerBounds.lower_from_representation v (translated z B k) B A E hb he
      (translated_represents q z B k hb hq) (le_congr (by ipra_ring) (.eqRefl _) base)
  exact le_congr (by ipra_ring) (.eqRefl _)
    (GaussianRationalLowerBounds.lower_to_cleared v (translated (rawGaussian q) (rawDen q) k) (rawDen q)
      A E (raw_den_positive q) he (translated_represents q _ _ k (raw_den_positive q) (raw_represents q)) n)

theorem raw_source (q z R B A E : PTm n) (hz : Γ ⊢[PRAAx] source z R B A E)
    (hq : Γ ⊢[PRAAx] represents q z B) : Γ ⊢[PRAAx] source (rawGaussian q) R (rawDen q) A E := by
  let w := rawGaussian q
  let D := rawDen q
  have hb := hz.andE₁.andE₂.andE₁
  have hd := raw_den_positive (Γ := Γ) q
  have hr := hz.andE₁.andE₁
  have disk : Γ ⊢[PRAAx] bounded q R one :=
    (bounded_iff q z B R one hb (le_refl one) hq).iffMpr
      (le_congr (by ipra_ring) (by ipra_ring) hz.andE₁.andE₂.andE₂)
  have newDisk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded w (R*D) :=
    le_congr (by ipra_ring) (by ipra_ring) ((bounded_iff q w D R one hd (le_refl one) (raw_represents q)).iffMp disk)
  refine .andI (.andI hr (.andI hd newDisk)) (.andI hz.andE₂.andE₁ (.andI hz.andE₂.andE₂.andE₁ ?_))
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have zs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaReciprocalInverse.subst_source] using hz.shift
  have qs : Δ ⊢[PRAAx] represents (sh q) (sh z) (sh B) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianRationalHorner.subst_represents] using hq.shift
  refine .allI (.impI ?_)
  simpa only [w,D,sh,Syn.shift,GaussianRationalL1.subst_rawGaussian,GaussianRationalL1.subst_rawDen,
    LeanProofs.IPRA.PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    raw_pole_at (sh q) (sh z) (sh R) (sh B) (sh A) (sh E) (var 0) zs.wk qs.wk Prf.hyp0

theorem raw_source_of_fraction (q z R B A E : PTm n) (hz : Γ ⊢[PRAAx] source z R B A E)
    (hq : Γ ⊢[PRAAx] q ≐ ofGaussian z B) : Γ ⊢[PRAAx] source (rawGaussian q) R (rawDen q) A E :=
  raw_source q z R B A E hz (represents_congr hq.eqSymm (equal_refl _) (.eqRefl _)
    (ofGaussian_represents z B hz.andE₁.andE₂.andE₁))

private theorem equal_at (p z w R B D E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B one E) (hw : Γ ⊢[PRAAx] source w R D one E)
    (hEq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 gammaF p (gammaData z R B E)) (ap2 gammaF p (gammaData w R D E)) (num 3) (unit p) := by
  let m := unit (modulus p R E)
  let U := unit p
  have hm := unit_positive (Γ := Γ) (modulus p R E)
  have hU := unit_positive (Γ := Γ) p
  have h := GaussianNameConjugation.equal_distance _ _ m hm hEq
  have near := distance_radius_mono_same hm (zero_le one) h
  have rate := GaussianGammaNamedPoleFreeModulus.original_rate p z w R B D E hz hw near
  exact distance_radius_mono _ _ _ _ (num 3) U (denominator_positive U p p hU) hU
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
    (rate_at gammaF gammaF _ _ one U p p rate)

theorem cross_equal_encoding (z w R B D E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B one E) (hw : Γ ⊢[PRAAx] source w R D one E)
    (hEq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    crossEquivalent gammaF gammaF (gammaData z R B E) (gammaData w R D E) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 3)
    (gamma_regular _ _ _ _ _ hz) (gamma_regular _ _ _ _ _ hw) (.allI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have zs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) one (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaReciprocalInverse.subst_source,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hz.shift
  have ws : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) one (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaReciprocalInverse.subst_source,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hw.shift
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,Fm.subst_eq,GaussianRationalHorner.subst_ofGaussian] using hEq.shift
  have sub (a b : PTm n) : Syn.subst (fun i => var i.succ) (gammaData a R b E) =
      gammaData (sh a) (sh R) (sh b) (sh E) := by
    simp [sh,Syn.shift,gammaData,GaussianGammaReciprocalInverse.gammaHeight]
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,sub,sh,Syn.shift,LeanProofs.IPRA.PTm.subst_num] using
    equal_at (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) (sh E) zs ws eq

theorem raw_gamma_cross (q z R B E : PTm n) (hz : Γ ⊢[PRAAx] source z R B one E)
    (hq : Γ ⊢[PRAAx] q ≐ ofGaussian z B) : Γ ⊢[PRAAx]
    crossEquivalent gammaF gammaF (gammaData (rawGaussian q) R (rawDen q) E) (gammaData z R B E) := by
  have raw := raw_source_of_fraction q z R B one E hz hq
  have hb := hz.andE₁.andE₂.andE₁
  have eq : Γ ⊢[PRAAx] ofGaussian (rawGaussian q) (rawDen q) ≐ ofGaussian z B :=
    (GaussianNameArithmetic.recode_congr hq).eqTrans
      (GaussianExponentialReference.recode_fixed _ (ofGaussian_canonical _ _ hb))
  exact cross_equal_encoding _ _ _ _ _ _ raw hz eq

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeEncoding
