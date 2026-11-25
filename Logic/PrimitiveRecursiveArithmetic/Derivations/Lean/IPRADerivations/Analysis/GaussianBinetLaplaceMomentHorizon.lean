import IPRADerivations.Analysis.GaussianBinetLaplaceMomentCompact
import IPRADerivations.Analysis.GaussianBinetLaplaceStripHorizon

/-!
# Horizon coherence of the actual weighted Binet moments

The weight is the same exact rational code on a common physical panel.
Each horizon pays for the weight at its own observation clock. The
original cofinal integrand coherence then survives weighted quadrature.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentHorizon

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input)
open GaussianBinetLaplaceMomentCompact (data compact_input wrapped_at)
open GaussianBinetLaplaceMomentFloor (weight clock observation gain fixedData evaluatorF nameF)
open GaussianBinetLaplaceStrip (Kernel source tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (inside evaluatorName nameData)
open GaussianDominantPairAlgebra (radius_bounded)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

private theorem weight_clock_budget (p j A B T : PTm n)
    (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] le (pw A j*unit p) (pw B j*unit (clock p j T)) := by
  have power := le_congr (.eqRefl _) (pw_mul_base T B j) (pw_le_pw j hT)
  have clockGrowth : Γ ⊢[PRAAx] le (pw T j*unit p) (unit (clock p j T)) :=
    GaussianFastValueCut.query_budget (pw T j) p
  exact le_trans (le_mul_mono power (le_refl (unit p)))
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (pw B j)) clockGrowth))

theorem observation_coherence (p q j X D R T S U A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (h' : Γ ⊢[PRAAx] input X zero D zero S U A B) :
    Γ ⊢[PRAAx] distanceBounded (observation p j X D R T A B) (observation q j X D S U A B)
      (unit p+unit q) (unit p*unit q) := by
  let r := clock p j T
  let s := clock q j U
  let x := cofinalData X zero D zero R T A B
  let y := cofinalData X zero D zero S U A B
  let a := ap2 cofinalF r x
  let b := ap2 cofinalF s y
  let w := weight j A B
  let C := pw A j
  let E := pw B j
  have hE : Γ ⊢[PRAAx] le one E :=
    GaussianPolynomialPerturbation.power_positive B j h.andE₂.andE₁
  have hr := unit_positive (Γ := Γ) r
  have hs := unit_positive (Γ := Γ) s
  have diff := cross_at cofinalF cofinalF x y r s
    (GaussianBinetLaplaceStripHorizon.integrand_coherence Kernel.cofinal X zero D zero R T S U zero A B h h')
  have mul := bounded_product w (qsub a b) C E (unit r+unit s) (unit r*unit s)
    hE (positive_product _ _ hr hs) (radius_bounded C E hE) diff
  have bound : Γ ⊢[PRAAx] distanceBounded (qmul w a) (qmul w b) (C*(unit r+unit s)) (E*(unit r*unit s)) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference w a b).eqSymm (.eqRefl _) (.eqRefl _) mul
  have advanceP : Γ ⊢[PRAAx] le (C*unit p) (E*unit r) := weight_clock_budget p j A B T h.andE₂.andE₂
  have advanceQ : Γ ⊢[PRAAx] le (C*unit q) (E*unit s) := weight_clock_budget q j A B U h'.andE₂.andE₂
  have rad : Γ ⊢[PRAAx] le ((C*(unit r+unit s))*(unit p*unit q))
      ((unit p+unit q)*(E*(unit r*unit s))) := by
    ipra_le 𝔞(unit q*unit s)*sl advanceP+𝔞(unit p*unit r)*sl advanceQ
  exact distance_congr (qmul_commutative w a) (qmul_commutative w b) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE (positive_product _ _ hr hs))
      (positive_product _ _ (unit_positive p) (unit_positive q)) rad bound)

theorem evaluator_coherence (t j X D R T S U : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T (tagNumerator t) (sndT t))
    (h' : Γ ⊢[PRAAx] input X zero D zero S U (tagNumerator t) (sndT t)) :
    Γ ⊢[PRAAx] crossEquivalent (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData j X D R T)) (nameData t (fixedData j X D S U)) := by
  let s (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have first : Δ ⊢[PRAAx] input (s X) zero (s D) zero (s R) (s T) (tagNumerator (s t)) (sndT (s t)) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,GaussianBinetLaplaceIntegrand.subst_input,
      GaussianBinetLaplaceStrip.subst_tagNumerator,subst_sndT,ConciseIPRA.PTm.subst_zero] using h.shift.shift
  have second : Δ ⊢[PRAAx] input (s X) zero (s D) zero (s S) (s U) (tagNumerator (s t)) (sndT (s t)) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,GaussianBinetLaplaceIntegrand.subst_input,
      GaussianBinetLaplaceStrip.subst_tagNumerator,subst_sndT,ConciseIPRA.PTm.subst_zero] using h'.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianCompactRiemannName.subst_nameData,GaussianBinetLaplaceMomentFloor.subst_fixedData,
    Syn.shift,s,Δ] using
    distance_congr (wrapped_at (Γ := Δ) (var 1) (s t) (s j) (s X) (s D) (s R) (s T)).eqSymm
      (wrapped_at (var 0) (s t) (s j) (s X) (s D) (s S) (s U)).eqSymm (.eqRefl _) (.eqRefl _)
      (observation_coherence (var 1) (var 0) (s j) (s X) (s D) (s R) (s T) (s S) (s U)
        (tagNumerator (s t)) (sndT (s t)) first second)

private theorem agreement_at (t j X D R T S U A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (h' : Γ ⊢[PRAAx] source X zero D zero S U A C E)
    (ht : Γ ⊢[PRAAx] inside (E+A) C E t) :
    Γ ⊢[PRAAx] crossEquivalent (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData j X D R T)) (nameData t (fixedData j X D S U)) :=
  evaluator_coherence t j X D R T S U
    (.andI h.andE₁ (.andI ht.andE₂.andE₁ (tag_inside t A C E T h.andE₂.andE₁ h.andE₂.andE₂ ht).andE₂))
    (.andI h'.andE₁ (.andI ht.andE₂.andE₁ (tag_inside t A C E U h'.andE₂.andE₁ h'.andE₂.andE₂ ht).andE₂))

theorem local_agreement (j X D R T S U A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (h' : Γ ⊢[PRAAx] source X zero D zero S U A C E) :
    Γ ⊢[PRAAx] GaussianCompactClientIndependence.localAgreement evaluatorF evaluatorF (E+A) C E
      (fixedData j X D R T) (fixedData j X D S U) := by
  let s (z : PTm n) := Syn.shift z
  let Δ := Γ.map Fm.shift
  have first : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,GaussianBinetLaplaceStrip.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift
  have second : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s S) (s U) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,GaussianBinetLaplaceStrip.subst_source,
      ConciseIPRA.PTm.subst_zero] using h'.shift
  refine .allI (.impI ?_)
  simpa only [GaussianCompactClientIndependence.localAgreement,GaussianCompactClientIndependence.agreementBody,
    GaussianBinetLaplaceMomentFloor.subst_fixedData,PTm.subst_add,Syn.shift,s,Δ] using
    agreement_at (var 0) (s j) (s X) (s D) (s R) (s T) (s S) (s U) (s A) (s C) (s E) first.wk second.wk Prf.hyp0

theorem coherence (j X D R T S U A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (h' : Γ ⊢[PRAAx] source X zero D zero S U A C E) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data j X D R T A C E) (data j X D S U A C E) :=
  GaussianCompactClientIndependence.name_independence evaluatorF evaluatorF (E+A) C E (gain j R T) T
    (gain j S U) U (fixedData j X D R T) (fixedData j X D S U)
    (.andI (compact_input j X D R T A C E h)
      (.andI (compact_input j X D S U A C E h') (local_agreement j X D R T S U A C E h h')))

theorem actual_weighted_Binet_strip_horizon_coherence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 1) zero (var 2) zero (var 3) (var 4) (var 7) (var 8) (var 9) ⟶
      source (var 1) zero (var 2) zero (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 7) (var 8) (var 9))
        (data (var 0) (var 1) (var 2) (var 5) (var 6) (var 7) (var 8) (var 9))) :=
  closeUniv 10 (.impI (.impI (coherence _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentHorizon
