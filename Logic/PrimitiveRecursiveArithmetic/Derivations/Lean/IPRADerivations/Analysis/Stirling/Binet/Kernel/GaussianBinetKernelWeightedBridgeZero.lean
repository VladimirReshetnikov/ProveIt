import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelWeightedBridge
import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetWeightedExponentialZero
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceZero

/-!
# The nonsingular weighted Binet kernel at zero time

The original decay observation is exactly one at zero. The original
weighted left quadrature has bias 1/(2*N), and its cofinal normalized
sampler is equivalent to zero. This extends the weighted identity
to all nonnegative rational times.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelWeightedBridgeZero

open_ipra
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerDecayMesh (observation)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF zero_at zero_fast)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "W" => GaussianBinetWeightedExponential.nameF
local notation "wd" => GaussianBinetWeightedExponential.data
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "kd" => GaussianBinetKernelRows.inputData
local notation "F" => GaussianBinetKernelWeightedBridge.nameF
local notation "fd" => GaussianBinetKernelWeightedBridge.data
local notation "Dg" => GaussianBinetKernelWeightedBridge.dampingF
local notation "dg" => GaussianBinetKernelWeightedBridge.dampingData

private theorem decay_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent decayF constantF (decayData zero B) qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianEulerDecayQuadraturePrecision.observation_regular zero B) (constant_regular _)
  refine .allI ?_
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift,one] using hB.shift
  have hz := GaussianEulerDecayQuadratureAtZero.zero_observation (Syn.shift B) (var 0) hb
  have e : Γ.map Fm.shift ⊢[PRAAx] observation zero (Syn.shift B) (var 0) ≐ ap2 constantF (var 0) qone :=
    hz.eqTrans (constant_at _ _).eqSymm
  simpa only [GaussianNameConjugation.pointwiseEqual,observation,Syn.shift,decayData,
    GaussianGammaFiniteApproximantName.exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianNameBounds.subst_U,GaussianEulerIntegrandName.subst_decayPoint,GaussianRationalSyntheticDivision.subst_qone,
    ConciseIPRA.PTm.subst_zero] using e

private theorem zero_const :
    Γ ⊢[PRAAx] crossEquivalent zeroF constantF (zero : PTm n) qzero := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,ConciseIPRA.PTm.subst_zero,
    GaussianRationalHorner.subst_qzero] using
    (zero_at (Γ := Γ.map Fm.shift) (var 0) zero).eqTrans (constant_at (var 0) qzero).eqSymm

private theorem kernel_damping_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent F zeroF (fd zero B) zero := by
  let x := kd zero B
  have hk := GaussianBinetKernelCofinal.regular zero B hB
  have diff : Γ ⊢[PRAAx] crossEquivalent Dg zeroF (dg zero B) zero :=
    GaussianNamedDifferenceZero.difference_zero _ _ _ _ _ (constant_regular _)
      (GaussianEulerDecayQuadraturePrecision.observation_regular zero B) (cross_symm _ _ _ _ (decay_zero B hB))
  have hd : Γ ⊢[PRAAx] crossEquivalent Dg constantF (dg zero B) qzero :=
    cross_trans _ _ _ _ _ _ diff zero_const
  have first := GaussianGammaAdjacentCutoff.multiply_cross Dg constantF K K (dg zero B) qzero x x
    (GaussianBinetKernelWeightedBridge.damping_regular zero B) (constant_regular _) hk hk hd (cross_refl _ _ hk)
  have last : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF K) zeroF
      (multiplyData constantF K qzero x) zero := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _
      (multiply_fast _ _ _ _ (constant_regular _) hk) (zero_fast _)
    refine .allI ?_
    have value := GaussianGammaRationalWendelBoundary.zero_product_at (Γ := Γ.map Fm.shift)
      K (var 0) qzero (Syn.shift x) (.eqRefl _)
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,x,GaussianNameArithmetic.subst_multiplyData,
      GaussianBoundedConstantProductName.constantF,GaussianGammaCanonicalExponent.constantF,
      GaussianRationalHorner.subst_qzero,ConciseIPRA.PTm.subst_zero] using
      value.eqTrans (zero_at (var 0) zero).eqSymm
  exact cross_trans _ _ _ _ _ _ first last

theorem weighted_zero_error (p B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 W p (wd zero B)) qzero one (unit p) := by
  let s := GaussianBinetWeightedExponential.clock p zero B
  let N := GaussianBinetWeightedExponential.mesh s zero
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have hn : Γ ⊢[PRAAx] le (unit p) N :=
    le_trans (GaussianExponentialReference.unit_monotone later) (le_add_left _ _)
  have e := GaussianBinetWeightedExponential.sample_at (Γ := Γ) p zero B
  exact distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBinetWeightedExponentialZero.cofinal_zero (s+N) p B N hB hn)

private theorem weighted_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent W zeroF (wd zero B) zero := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let X := Syn.shift (Syn.shift B)
  have hb : Δ ⊢[PRAAx] le one X := by simpa [Δ,X,Fm.shift,Syn.shift,one] using hB.shift.shift
  have hp := unit_positive (Γ := Δ) p
  have hq := unit_positive (Γ := Δ) q
  have e := distance_congr (.eqRefl _) (zero_at (Γ := Δ) q zero).eqSymm (.eqRefl _) (.eqRefl _)
    (weighted_zero_error p X hb)
  have bound : Δ ⊢[PRAAx] le (one*(unit p*unit q)) ((unit p+unit q)*unit p) := by
    apply le_of_eq_add (d := unit p*unit p)
    ipra_ring
  have result := distance_radius_mono _ _ _ _ _ _ hp (positive_product _ _ hp hq) bound e
  simpa only [crossEquivalent,Δ,p,q,X,Syn.shift,GaussianBinetWeightedExponential.subst_data,
    ConciseIPRA.PTm.subst_zero] using result

theorem at_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent F W (fd zero B) (wd zero B) :=
  cross_trans _ _ _ _ _ _ (kernel_damping_zero B hB) (cross_symm _ _ _ _ (weighted_zero B hB))

theorem equivalent (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent F W (fd A B) (wd A B) := by
  refine .orE (zero_or_succ A) ?_ ?_
  · let Δ := (A ≐ zero)::Γ
    let φ := crossEquivalent F W (fd (var 0) (Syn.shift B)) (wd (var 0) (Syn.shift B))
    have hzero := at_zero B (Γ := Δ) hB.wk
    have e : Δ ⊢[PRAAx] zero ≐ A := Prf.hyp0.eqSymm
    have hz : Δ ⊢[PRAAx] φ.subst (Syn.inst zero) := by
      simpa only [φ,GaussianNameEquivalence.subst_crossEquivalent,GaussianBinetKernelWeightedBridge.subst_data,
        GaussianBinetWeightedExponential.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hzero
    simpa only [φ,GaussianNameEquivalence.subst_crossEquivalent,GaussianBinetKernelWeightedBridge.subst_data,
      GaussianBinetWeightedExponential.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.eqSubst1 φ e hz
  · have ha : (A ≐ succ (pred A))::Γ ⊢[PRAAx] le one A :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact GaussianBinetKernelWeightedBridge.positive_time_bridge A B ha hB.wk

theorem weighted_regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN W (wd A B) := by
  have h := equivalent A B hB
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ h) h

theorem actual_Binet_weighted_kernel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent F W (fd (var 0) (var 1)) (wd (var 0) (var 1))) :=
  closeUniv 2 (.impI (equivalent _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelWeightedBridgeZero
