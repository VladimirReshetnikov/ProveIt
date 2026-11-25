import IPRADerivations.Analysis.GaussianGammaNamedPoleFreeProperness
import IPRADerivations.Analysis.GaussianNamedGammaSmallIncrementInput
import IPRADerivations.Analysis.GaussianEulerBetaPolynomialPrimitive
import IPRADerivations.Analysis.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.GaussianSineReflectionLower

/-!
# Pole separation under a small named increment

A perturbation of magnitude at most 1/(2E) leaves each original pole
gap at least 1/(2E). The actual normalized sum reads both input names
at the same clock, so this preserves the source on the enlarged disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeIncrementSource

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianFastValueCut (recode_bound_iff)
open GaussianGammaEulerHeadLower (poleAt translated)
open GaussianGammaNamedPoleFree (source source_at)
open GaussianGammaNamedPoleFreeProperness (every_pole_at)
open GaussianNameArithmetic (sum_distance)
open GaussianNamedGammaIncrementInput (clock)
open GaussianNamedGammaSmallIncrementInput (sample_at regular)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd canonical_unique ofGaussian_represents positive_product represents represents_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalLowerBounds (lower lower_from_representation lower_to_cleared)
open GaussianRationalMetric (bounded bounded_of_cleared bounded_to_cleared distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerDifference (bounded_sum_same distance_refl_zero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalSyntheticCoefficientValues (qadd_recode_left qadd_sub_recode)
open GaussianSineReflectionLower (lower_after_half_error)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "native" => GaussianGammaReciprocalInverse.source
local notation "SF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "sd" => GaussianNamedGammaSmallIncrementInput.sumData

private theorem recodes_agree (q : PTm n) : Γ ⊢[PRAAx]
    GaussianFastValueCut.recode q ≐ GaussianTranslatedNonconstant.recode q :=
  canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical q) (GaussianTranslatedNonconstant.recode_canonical q)
    (raw_den_positive q) (GaussianFastValueCut.recode_represents q) (GaussianTranslatedNonconstant.recode_represents q)

private theorem shifted_represents (q j : PTm n) : Γ ⊢[PRAAx]
    represents (qadd q (naturalPoint j)) (translated (rawGaussian q) (rawDen q) j) (rawDen q) := by
  have h := raw_den_positive (Γ := Γ) q
  have e := (GaussianEulerBetaPolynomialPrimitive.linear_as_sum (rawGaussian q) (rawDen q) j h).eqTrans
    ((qadd_congr (recodes_agree q) (.eqRefl _)).eqTrans (qadd_recode_left q (naturalPoint j)))
  exact represents_congr e (GaussianRootAlgebra.equal_refl _) (.eqRefl _) (ofGaussian_represents _ _ h)

private theorem increment_pole_at (q u R E j : PTm n) (hq : Γ ⊢[PRAAx] native (rawGaussian q) R (rawDen q) one E)
    (hu : Γ ⊢[PRAAx] bounded u one (two*E)) : Γ ⊢[PRAAx]
    poleAt (rawGaussian (qadd q u)) (rawDen (qadd q u)) one (two*E) j := by
  let r := qadd q u
  let J := naturalPoint j
  let B := two*E
  have he := positive_product (Γ := Γ) two E (le_succ_self one) hq.andE₂.andE₂.andE₁
  have base := every_pole_at (rawGaussian q) R (rawDen q) E j hq
  have old : Γ ⊢[PRAAx] lower (qadd q J) (two*one) B :=
    lower_from_representation _ _ _ _ _ (raw_den_positive q) he (shifted_represents q j)
      (le_congr (by ipra_ring) (by unfold B; ipra_ring) (mul_le_mul_right (two*two) base))
  have d : Γ ⊢[PRAAx] distanceBounded r q one B :=
    bound_congr ((qadd_sub_recode q u).eqTrans (recodes_agree u).eqSymm).eqSymm (.eqRefl _) (.eqRefl _)
      ((recode_bound_iff u one B he).iffMpr hu)
  have step : Γ ⊢[PRAAx] distanceBounded (qadd q J) (qadd r J) one B :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (sum_distance q r J J one zero B he (distance_symmetric _ _ _ _ he d) (distance_refl_zero J B he))
  have keep := lower_after_half_error (qadd q J) (qadd r J) one B he old step
  exact le_congr (by ipra_ring) (.eqRefl _)
    (lower_to_cleared _ _ _ _ _ (raw_den_positive r) he (shifted_represents r j) keep)

theorem native_increment (q u R E : PTm n) (hq : Γ ⊢[PRAAx] native (rawGaussian q) R (rawDen q) one E)
    (hu : Γ ⊢[PRAAx] bounded u one (two*E)) : Γ ⊢[PRAAx]
    native (rawGaussian (qadd q u)) (succ R) (rawDen (qadd q u)) one (two*E) := by
  let r := qadd q u
  have he := positive_product (Γ := Γ) two E (le_succ_self one) hq.andE₂.andE₂.andE₁
  have base : Γ ⊢[PRAAx] bounded q R one :=
    bounded_of_cleared _ _ _ _ _ (raw_den_positive q) (le_refl one) (raw_represents q)
      (le_congr (by ipra_ring) (by ipra_ring) hq.andE₁.andE₂.andE₂)
  have small : Γ ⊢[PRAAx] bounded u one one :=
    bounded_radius_mono u one (two*E) one one he (le_refl one) (le_congr (one_mul _).eqSymm (one_mul _).eqSymm he) hu
  have sum : Γ ⊢[PRAAx] bounded r (succ R) one :=
    bound_congr (.eqRefl _) (succ_eq_add_one R).eqSymm (.eqRefl _) (bounded_sum_same q u R one one (le_refl one) base small)
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (rawGaussian r) (succ R*rawDen r) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (bounded_to_cleared _ _ _ _ _ (raw_den_positive r) (le_refl one) (raw_represents r) sum)
  refine .andI (.andI (le_trans hq.andE₁.andE₁ (le_succ_self R)) (.andI (raw_den_positive r) disk))
    (.andI (le_refl one) (.andI he (.allI (.impI ?_))))
  let sh (a : PTm n) := Syn.shift a
  let Δ := le (var 0) (sh (two*succ R)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] native (rawGaussian (sh q)) (sh R) (rawDen (sh q)) one (sh E) :=
    by simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaReciprocalInverse.subst_source,
      GaussianRationalL1.subst_rawGaussian,GaussianRationalL1.subst_rawDen,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hq.shift.wk
  have small' : Δ ⊢[PRAAx] bounded (sh u) one (two*sh E) :=
    by simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianRationalMetric.subst_bounded,PTm.subst_mul,one,two,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hu.shift.wk
  simpa only [Δ,sh,Syn.shift,r,GaussianRationalL1.subst_rawGaussian,GaussianRationalL1.subst_rawDen,
    GaussianRationalHorner.subst_qadd,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    increment_pole_at (sh q) (sh u) (sh R) (sh E) (var 0) hs small'

theorem observed_source (f K : PR 2) (p x z R E : PTm n) (hf : Γ ⊢[PRAAx] source f x R E)
    (hu : Γ ⊢[PRAAx] smallSamples K z one (two*E)) : Γ ⊢[PRAAx]
    native (rawGaussian (ap2 (SF f K) p (sd x z))) (succ R)
      (rawDen (ap2 (SF f K) p (sd x z))) one (two*E) := by
  let q := ap2 f (clock p) x
  let u := ap2 K (clock p) z
  let S := ap2 (SF f K) p (sd x z)
  have original := native_increment q u R E (source_at f (clock p) x R E hf)
    (small_samples_at K z one (two*E) (clock p) hu)
  have moved := Prf.eqSubst1 (Γ := Γ) (Ax := PRAAx)
    (native (rawGaussian (var 0)) (Syn.shift (succ R)) (rawDen (var 0)) one (Syn.shift (two*E)))
    (s := qadd q u) (t := S) (sample_at f K p x z).eqSymm (by
      simpa only [GaussianGammaReciprocalInverse.subst_source,GaussianRationalL1.subst_rawGaussian,
        GaussianRationalL1.subst_rawDen,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,one,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using original)
  simpa only [GaussianGammaReciprocalInverse.subst_source,GaussianRationalL1.subst_rawGaussian,
    GaussianRationalL1.subst_rawDen,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using moved

theorem original_source (f K : PR 2) (x z R E : PTm n) (hf : Γ ⊢[PRAAx] source f x R E)
    (hk : Γ ⊢[PRAAx] pointCN K z) (hu : Γ ⊢[PRAAx] smallSamples K z one (two*E)) :
    Γ ⊢[PRAAx] source (SF f K) (sd x z) (succ R) (two*E) := by
  refine .andI (regular f K x z hf.andE₁ hk) (.allI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have base : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaNamedPoleFree.subst_source] using hf.shift
  have small : Δ ⊢[PRAAx] smallSamples K (sh z) one (two*sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianExponentialSmallPerturbation.subst_smallSamples,PTm.subst_mul,one,two,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hu.shift
  simpa only [Syn.shift,sh,GaussianNamedGammaSmallIncrementInput.subst_sumData,PTm.subst_mul,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observed_source f K (var 0) (sh x) (sh z) (sh R) (sh E) base small

theorem actual_named_Gamma_pole_free_small_increment_source_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) (var 3) ⋏ (pointCN K (var 1) ⋏ smallSamples K (var 1) one (two*var 3))) ⟶
        source (SF f K) (sd (var 0) (var 1)) (succ (var 2)) (two*var 3)) :=
  closeUniv 4 (.impI (original_source f K _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeIncrementSource
