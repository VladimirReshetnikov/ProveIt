import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentFloor
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference

/-!
# Compact regularity of the actual weighted Binet moments

The exact rational time power and the original cofinal Binet product
obey a common spatial modulus. The retiming in the weighted evaluator
pays for amplification of both independent observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentCompact

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData meshGain)
open GaussianBinetLaplaceMomentFloor
  (weight clock observation gain fixedData evaluatorF evaluator_at nameF unitPanelData)
open GaussianBinetLaplaceStrip (source tagNumerator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (inside value evaluatorName nameData localBody sampledModulus)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded radius_power)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate
  (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (budget bounded_power_integer power_distance_bound)
open GaussianRationalReciprocal (power bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

private theorem time_radius (A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le A (T*B)) : Γ ⊢[PRAAx] bounded (radiusPoint A B) T one :=
  bounded_radius_mono _ _ _ _ _ hB (le_refl one) (le_congr (by ipra_ring) (.eqRefl _) h)
    (radius_bounded A B hB)

theorem weight_bound (j A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le A (T*B)) : Γ ⊢[PRAAx] bounded (weight j A B) (pw T j) one :=
  bound_congr (radius_power A B j hB) (.eqRefl _) (.eqRefl _)
    (bounded_power_integer (radiusPoint A B) T j (time_radius A B T hB h))

theorem weight_distance (j A B a b T M Q : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source A B a b T M Q) :
    Γ ⊢[PRAAx] distanceBounded (weight j A B) (weight j a b) (budget T M j) Q := by
  have hb := h.andE₂.andE₁
  have hq := h.andE₂.andE₂.andE₁
  have hA := h.andE₂.andE₂.andE₂.andE₁
  have ha := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have dd := distance_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B h.andE₁)
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb) (.eqRefl _) (.eqRefl _)
    h.andE₂.andE₂.andE₂.andE₂.andE₂
  exact distance_congr (radius_power A B j h.andE₁) (radius_power a b j hb) (.eqRefl _) (.eqRefl _)
    (power_distance_bound (radiusPoint A B) (radiusPoint a b) T M Q j hq
      (time_radius A B T h.andE₁ hA) (time_radius a b T hb ha) dd)

private theorem retiming_budget (p q j R T M Q : PTm n) :
    let r := clock p j T
    let s := clock q j T
    Γ ⊢[PRAAx] le
      ((rateNumerator (meshGain R T*M) Q r s*pw T j+budget T M j*(unit r*unit s))*rateDenominator Q p q)
      (rateNumerator (gain j R T*M) Q p q*rateDenominator Q r s) := by
  let r := clock p j T
  let s := clock q j T
  have pr : Γ ⊢[PRAAx] le (pw T j*unit p) (unit r) := GaussianFastValueCut.query_budget (pw T j) p
  have qs : Γ ⊢[PRAAx] le (pw T j*unit q) (unit s) := GaussianFastValueCut.query_budget (pw T j) q
  change Γ ⊢[PRAAx] le
      ((rateNumerator (meshGain R T*M) Q r s*pw T j+budget T M j*(unit r*unit s))*rateDenominator Q p q)
      (rateNumerator (gain j R T*M) Q p q*rateDenominator Q r s)
  unfold rateNumerator rateDenominator gain budget
  ipra_le 𝔞(Q*Q*unit q*unit s)*sl pr+𝔞(Q*Q*unit p*unit r)*sl qs

theorem observation_rate (p q j X D R T A B a b M Q : PTm n)
    (hz : Γ ⊢[PRAAx] realSource X zero D zero R)
    (ht : Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source A B a b T M Q) :
    Γ ⊢[PRAAx] distanceBounded (observation p j X D R T A B) (observation q j X D R T a b)
      (rateNumerator (gain j R T*M) Q p q) (rateDenominator Q p q) := by
  let r := clock p j T
  let s := clock q j T
  let x := cofinalData X zero D zero R T A B
  let y := cofinalData X zero D zero R T a b
  let W := pw T j
  let S := unit r*unit s
  let E := rateDenominator Q r s
  have hb := ht.andE₂.andE₁
  have hq := ht.andE₂.andE₂.andE₁
  have hA := ht.andE₂.andE₂.andE₂.andE₁
  have ha := ht.andE₂.andE₂.andE₂.andE₂.andE₁
  have epos : Γ ⊢[PRAAx] le one E := denominator_positive Q r s hq
  have base := rate_at cofinalF cofinalF x y (meshGain R T*M) Q r s
    (GaussianBinetLaplaceIntegrand.cofinal_time_rate X zero D zero R T A B a b M Q hz ht)
  have weighted : Γ ⊢[PRAAx] distanceBounded (weight j A B) (weight j a b) (budget T M j*S) E :=
    distance_radius_mono _ _ _ _ _ _ hq epos
      (le_of_eq_add (d := zero) (by dsimp only [E,S,rateDenominator]; ipra_ring))
      (weight_distance j A B a b T M Q ht)
  have bb := bounded_radius_mono (ap2 cofinalF s y) one two one one
    (le_succ_self one) (le_refl one) (by ipra_le 1)
    (GaussianBinetLaplaceIntegrand.cofinal_bound s X zero D zero R T a b (.andI hz (.andI hb ha)))
  have prod := GaussianNameArithmetic.product_distance (ap2 cofinalF r x) (ap2 cofinalF s y)
    (weight j A B) (weight j a b) _ _ E W one epos base weighted
    (weight_bound j A B T ht.andE₁ hA) bb
  have bound := distance_congr (.eqRefl _) (.eqRefl _)
    (by ipra_ring : Γ ⊢[PRAAx] _ ≐ rateNumerator (meshGain R T*M) Q r s*W+budget T M j*S)
    (.eqRefl _) prod
  exact distance_radius_mono _ _ _ _ _ _ epos (denominator_positive Q p q hq)
    (retiming_budget p q j R T M Q) bound

def data (j X D R T A C E : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (E+A) C E (gain j R T) T (fixedData j X D R T)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (j X D R T A C E : PTm n) :
    Syn.subst σ (data j X D R T A C E) =
      data (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R)
        (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by
  simp [data]

theorem wrapped_at (p t j X D R T : PTm n) :
    Γ ⊢[PRAAx] ap2 (evaluatorName evaluatorF) p (nameData t (fixedData j X D R T)) ≐
      observation p j X D R T (tagNumerator t) (sndT t) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_at p t j X D R T)

theorem local_modulus_at (j X D R T A C E t u M Q : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hQ : Γ ⊢[PRAAx] le one Q)
    (ht : Γ ⊢[PRAAx] inside (E+A) C E t) (hu : Γ ⊢[PRAAx] inside (E+A) C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) M Q) :
    Γ ⊢[PRAAx] independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData j X D R T)) (nameData u (fixedData j X D R T)) (gain j R T*M) Q := by
  let s (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have sourceShift : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) :=
    by simpa [Δ,Fm.shift,Syn.shift,s] using h.andE₁.shift.shift
  have hs := GaussianBinetLaplaceStrip.tag_source t u A C E T M Q h.andE₂.andE₁ h.andE₂.andE₂ hQ ht hu hd
  have tagShift : Δ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source (tagNumerator (s t)) (sndT (s t))
      (tagNumerator (s u)) (sndT (s u)) (s T) (s M) (s Q) :=
    by simpa [Δ,Fm.shift,Syn.shift,s,GaussianBinetLaplaceStrip.tagNumerator] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,s,GaussianCompactRiemannName.subst_nameData,
    GaussianBinetLaplaceMomentFloor.subst_fixedData,GaussianBinetLaplaceMomentFloor.subst_gain,PTm.subst_mul,Δ] using
    distance_congr (wrapped_at (Γ := Δ) (var 1) (s t) (s j) (s X) (s D) (s R) (s T)).eqSymm
      (wrapped_at (var 0) (s u) (s j) (s X) (s D) (s R) (s T)).eqSymm (.eqRefl _) (.eqRefl _)
      (observation_rate (var 1) (var 0) (s j) (s X) (s D) (s R) (s T) (tagNumerator (s t)) (sndT (s t))
        (tagNumerator (s u)) (sndT (s u)) (s M) (s Q) sourceShift tagShift)

theorem sampled_modulus (j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] sampledModulus evaluatorF (E+A) C E (gain j R T) (fixedData j X D R T) := by
  let s (z : PTm n) := Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,GaussianBinetLaplaceStrip.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,Syn.shift,s,GaussianBinetLaplaceMomentFloor.subst_fixedData,
    GaussianBinetLaplaceMomentFloor.subst_gain,PTm.subst_add,Δ] using
    local_modulus_at (s j) (s X) (s D) (s R) (s T) (s A) (s C) (s E)
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF (E+A) C E (gain j R T) T (fixedData j X D R T) :=
  .andI (le_trans h.andE₂.andE₁ (le_add_right E A)) (.andI h.andE₂.andE₁
    (.andI (le_trans (le_add_left C A) h.andE₂.andE₂) (sampled_modulus j X D R T A C E h)))

theorem regular (j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] pointCN nameF (data j X D R T A C E) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input j X D R T A C E h)

theorem unit_panel_regular (j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] pointCN nameF (unitPanelData j X D R) :=
  regular j X D R two one one one (.andI h (.andI (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring))))

theorem actual_weighted_Binet_compact_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) zero (var 2) zero (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (regular _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentCompact
