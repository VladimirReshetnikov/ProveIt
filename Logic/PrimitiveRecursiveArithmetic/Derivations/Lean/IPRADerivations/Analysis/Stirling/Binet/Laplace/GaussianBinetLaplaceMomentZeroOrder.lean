import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentImproper
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceImproperName
import IPRADerivations.Analysis.Integration.GaussianCompactClientIndependence
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceStripHorizon

/-!
# The zeroth actual Binet moment is the original Binet improper name

The exact zero power turns the moment evaluator into the original
cofinal Binet integrand after a later read. Compact client
independence equates the corresponding panels. The two original
improper samplers exhaust the same panels.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentZeroOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input meshGain)
open GaussianBinetLaplaceMomentFloor (weight clock observation fixedData evaluatorF gain)
open GaussianBinetLaplaceMomentCompact (wrapped_at compact_input)
open GaussianBinetLaplaceStrip (Kernel tagNumerator tag_inside source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (evaluatorName nameData)
open GaussianDominantPairAlgebra (radiusPoint radius_one)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "MF" => GaussianBinetLaplaceMomentFloor.nameF
local notation "UF" => GaussianBinetLaplaceStrip.nameF Kernel.cofinal
local notation "Ueval" => GaussianBinetLaplaceStrip.evaluatorF Kernel.cofinal
local notation "UJ" => GaussianBinetLaplaceImproperName.nameF
local notation "UD" => GaussianBinetLaplaceImproperName.data
local notation "MJ" => GaussianBinetLaplaceMomentImproper.nameF
local notation "MD" => GaussianBinetLaplaceMomentImproper.data
local notation "uprefix" => GaussianBinetLaplaceOrderedPrefixes.prefixData
local notation "mprefix" => GaussianBinetLaplaceMomentPrefixes.prefixData
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem observation_zero (p X D R T A B : PTm n) :
    Γ ⊢[PRAAx] observation p zero X D R T A B ≐
      ap2 cofinalF (clock p zero T) (cofinalData X zero D zero R T A B) := by
  let r := clock p zero T
  let f := GaussianBinetKernelCofinal.nameF
  let x := GaussianBinetLaplaceExponential.data X zero D zero R T A B
  let y := GaussianBinetKernelRows.inputData A B
  let q := ap2 cofinalF r (cofinalData X zero D zero R T A B)
  have w : Γ ⊢[PRAAx] weight zero A B ≐ qone :=
    (GaussianDominantPairAlgebra.radius_congr (pw_zero A) (pw_zero B)).eqTrans radius_one
  have can := GaussianRationalHorner.canonical_congr (GaussianBinetLaplaceIntegrand.product_at (Γ := Γ) f r x y)
    (qmul_canonical _ _)
  exact (qmul_congr (.eqRefl q) w).eqTrans (GaussianReciprocalHorner.qmul_one_right q can)

private theorem observation_rate (p q X D R T A B : PTm n) (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] distanceBounded (observation p zero X D R T A B)
      (ap2 cofinalF q (cofinalData X zero D zero R T A B)) (unit p+unit q) (unit p*unit q) := by
  let r := clock p zero T
  let x := cofinalData X zero D zero R T A B
  have read := GaussianNameEquivalence.point_at cofinalF x r q
    (GaussianBinetLaplaceIntegrand.cofinal_regular X zero D zero R T A B h)
  have later : Γ ⊢[PRAAx] le (unit p) (unit r) :=
    GaussianExponentialReference.unit_monotone (le_add_right p (GaussianFastValueCut.normalizer (pw T zero)))
  apply distance_congr (observation_zero p X D R T A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive r) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) ?_ read
  ipra_le 𝔞(unit q)*𝔞(unit q)*sl later

private theorem tag_cross (t X D R T : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T (tagNumerator t) (sndT t)) :
    Γ ⊢[PRAAx] crossEquivalent (evaluatorName evaluatorF) (evaluatorName Ueval)
      (nameData t (fixedData zero X D R T))
      (nameData t (GaussianBinetLaplaceStrip.fixedData X zero D zero R T zero)) := by
  let s (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h' : Δ ⊢[PRAAx] input (s X) zero (s D) zero (s R) (s T) (tagNumerator (s t)) (sndT (s t)) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceIntegrand.subst_input,GaussianBinetLaplaceStrip.subst_tagNumerator,
      subst_sndT,ConciseIPRA.PTm.subst_zero] using h.shift.shift
  refine .allI (.allI ?_)
  have rw := wrapped_at (Γ := Δ) (var 1) (s t) zero (s X) (s D) (s R) (s T)
  have ru := GaussianBinetLaplaceStrip.wrapped_at (Γ := Δ) Kernel.cofinal (var 0) (s t)
    (s X) zero (s D) zero (s R) (s T) zero
  simpa only [crossEquivalent,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_nameData,
    GaussianBinetLaplaceMomentFloor.subst_fixedData,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
    ConciseIPRA.PTm.subst_zero,GaussianBinetLaplaceStrip.integrandF,GaussianBinetLaplaceStrip.integrandData] using
    distance_congr rw.eqSymm ru.eqSymm (.eqRefl _) (.eqRefl _)
      (observation_rate (var 1) (var 0) (s X) (s D) (s R) (s T) (tagNumerator (s t)) (sndT (s t)) h')

private theorem agreement (X D R T A C E : PTm n) (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] GaussianCompactClientIndependence.localAgreement evaluatorF Ueval (E+A) C E
      (fixedData zero X D R T) (GaussianBinetLaplaceStrip.fixedData X zero D zero R T zero) := by
  let s (z : PTm n) := Syn.shift z
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift
  refine .allI (.impI ?_)
  let t : PTm (n+1) := var 0
  have ht : (GaussianCompactRiemannName.inside (s E+s A) (s C) (s E) t)::Δ ⊢[PRAAx]
      GaussianCompactRiemannName.inside (s E+s A) (s C) (s E) t := Prf.hyp0
  have ih := (tag_inside t (s A) (s C) (s E) (s T) hs.andE₂.andE₁.wk hs.andE₂.andE₂.wk ht).andE₂
  simpa only [GaussianCompactClientIndependence.localAgreement,GaussianCompactClientIndependence.agreementBody,
    GaussianBinetLaplaceMomentFloor.subst_fixedData,GaussianCompactRiemannName.subst_sampleData,
    subst_pairT,PTm.subst_add,Syn.shift,s,Δ,t,ConciseIPRA.PTm.subst_zero] using
    tag_cross t (s X) (s D) (s R) (s T) (.andI hs.andE₁.wk (.andI ht.andE₂.andE₁ ih))

theorem compact_equivalent (X D R T A C E : PTm n) (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] crossEquivalent MF UF (GaussianBinetLaplaceMomentCompact.data zero X D R T A C E)
      (GaussianBinetLaplaceStrip.data X zero D zero R T zero A C E) :=
  GaussianCompactClientIndependence.name_independence evaluatorF Ueval (E+A) C E (gain zero R T) T (meshGain R T) T
    (fixedData zero X D R T) (GaussianBinetLaplaceStrip.fixedData X zero D zero R T zero)
    (.andI (compact_input zero X D R T A C E h)
      (.andI (GaussianBinetLaplaceStrip.compact_input Kernel.cofinal X zero D zero R T zero A C E h)
        (agreement X D R T A C E h)))

private theorem two_per_clock (a b p : PTm n) (h : Γ ⊢[PRAAx] distanceBounded a b (unit p+unit p) (unit p*unit p)) :
    Γ ⊢[PRAAx] distanceBounded a b two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem improper_diagonal (p X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 MJ p (MD zero X D R)) (ap2 UJ p (UD X zero D zero R)) (num 6) (unit p) := by
  let a := GaussianBinetLaplaceMomentImproper.cutoff p zero D
  let b := GaussianBinetLaplaceImproperName.cutoff p D
  let L := a+b
  let W := GaussianBinetLaplaceOrderedPrefixes.width D L
  let m := mprefix zero X D R W
  let u := uprefix X zero D zero R L
  have hw : Γ ⊢[PRAAx] le L W := le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_mul_mono h.andE₁.andE₂ (le_refl L)) (le_refl one))
  have first := two_per_clock _ _ p
    (GaussianBinetLaplaceMomentImproper.late_observations p p zero X D R W h (le_trans (le_add_right a b) hw))
  have chart : Γ ⊢[PRAAx] source X zero D zero R W zero W one :=
    .andI h (.andI (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) (le_refl W)))
  have center := two_per_clock _ _ p
    (cross_at MF UF m u p p (compact_equivalent X D R W zero W one chart))
  have last := two_per_clock _ _ p
    (GaussianBinetLaplaceImproperName.late_observations p p X zero D zero R L h (le_add_left b a))
  have hp := unit_positive (Γ := Γ) p
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp
      (distance_triangle_same _ _ _ _ _ _ hp first center)
      (distance_symmetric _ _ _ _ hp last))

theorem improper_equivalent (X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] crossEquivalent MJ UJ (MD zero X D R) (UD X zero D zero R) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianBinetLaplaceMomentImproper.regular zero X D R h)
    (GaussianBinetLaplaceImproperName.regular X zero D zero R h)
  refine .allI ?_
  let s (z : PTm n) := Syn.shift z
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Δ,s,Syn.shift,
    GaussianBinetLaplaceMomentImproper.subst_data,GaussianBinetLaplaceImproperName.subst_data,
    ConciseIPRA.PTm.subst_zero,LeanProofs.IPRA.PTm.subst_num] using
    improper_diagonal (var 0) (s X) (s D) (s R) hs

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentZeroOrder
