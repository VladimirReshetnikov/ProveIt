import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondFormulaReduction
import IPRADerivations.Analysis.Stirling.Binet.Bose.ImproperNames.GaussianBinetBoseLateSchedule
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.Tails.GaussianBinetSecondDecayRetiming
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.WeightedSine.Schedules.GaussianBinetSecondFrequencySchedule
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondErrorBudget
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineKernels.GaussianBinetSineKernelPrefix
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.FrozenKernels.GaussianBinetFrozenKernelLaplace

/-!
# Binet's second formula for the original improper Bose integral

All intermediate observations use the same time and frequency tags
where they are compared. The angular schedule is chosen before the
literal Bose refinement, so the final mesh and clock can pay both
analytic and arithmetic errors without changing either cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondFormula

open_ipra
open GaussianBinetBoseFrozenSuffix (fullMesh)
open GaussianBinetBoseImproperName (source)
open GaussianBinetBoseLateSchedule
  (originClock compactClock extraRows literalClock piClock meshBase frozenClock
    origin_bounds pi_bounds mesh_bounds frozen_bounds)
open GaussianBinetFirstFormulaDecay (laplaceData subst_laplaceData)
open GaussianBinetSecondEarlySchedule
  (index timeHorizon kernelCutoff stripDenominator angularAccuracy frequencyCutoff frequencyHorizon)
open GaussianBinetSecondFrequencySchedule (kernelClock laplaceClock)
open GaussianBinetSecondErrorBudget (fit double_distance)
open GaussianBinetSecondWeightedSineCut (cut certificates count_width_budget)
open GaussianBinetSecondWeightedSineTransposedPrefix (transposedPrefix)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNameEquivalence (crossEquivalent)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "First" => GaussianBinetLaplaceImproperName.nameF
local notation "Second" => GaussianBinetSecondFormulaReduction.nameF
local notation "secondData" => GaussianBinetSecondFormulaReduction.data
local notation "Bose" => GaussianBinetBoseImproperName.nameF
local notation "boseData" => GaussianBinetBoseImproperName.data

theorem observation_error (p X Y D sign K : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 First p (laplaceData X Y D sign))
      (ap2 Second p (secondData X Y D sign K)) (num 35) (unit p) := by
  let R := GaussianLogGammaEulerResidualRadius.radius X Y
  let T := timeHorizon p D K
  let I := kernelCutoff p D K
  let E := stripDenominator p D K
  let q := angularAccuracy p D K
  let L := frequencyCutoff p D K
  let S := D*L
  let A := GaussianBinetSecondFrequencySchedule.radius p q I E D R T K
  let s := GaussianBinetArctangentSineUniform.clock q D A T K
  let N := GaussianBinetArctangentSineUniform.count q D A T K
  let c := cut q D A T K E
  let r := kernelClock p S
  let l := laplaceClock p D L
  let v := originClock p D K I
  let a := compactClock p D T v
  let J := I+extraRows a v
  let u := literalClock p a K T v J
  let kMin := GaussianFastValueCut.exponent I r
  let meshMin := unit (s+N)+((num 10*I+S)*T)
  let k := piClock u J T kMin
  let B := meshBase a D T v J k meshMin
  let M := fullMesh T (GaussianBinetBoseOriginExhaustion.cutoff v) B
  let b := frozenClock p u T v J k M q
  let U := unit p
  let z := ap2 Second p (secondData X Y D sign K)
  let y := ap2 First p (laplaceData X Y D sign)
  let f := GaussianBinetBoseFrozenMatrix.value b k I M X Y D sign zero T one
  let g := GaussianBinetSecondWeightedSinePrefix.value q k I M T X Y D sign A K
  let f' := qmul (fraction two one) f
  let g' := qmul (fraction two one) g
  let x := transposedPrefix q k I M T X Y D sign A K c
  let m := GaussianBinetFrozenKernelRectangle.value s k I N S c X Y D sign A
  let w := GaussianBinetLaplaceFrequencySuffix.suffixValue l N X Y D sign R L c
  have hR := GaussianLogGammaEulerResidualRadius.source_of_right_half_plane X Y D sign h.andE₁
  have hX : Γ ⊢[PRAAx] le one X := hR.andE₁.andE₁.andE₁
  have hD : Γ ⊢[PRAAx] le one D := hR.andE₁.andE₂
  have hK : Γ ⊢[PRAAx] le one K :=
    GaussianDominantScalarOrder.factor_positive_left K X (le_trans hD h.andE₂)
  have hT : Γ ⊢[PRAAx] le one T := unit_positive _
  have hI : Γ ⊢[PRAAx] le one I := unit_positive _
  have hQ : Γ ⊢[PRAAx] le (two*E) (unit q) :=
    le_congr (.eqRefl _) (GaussianBinetSecondEarlySchedule.double_strip p D K) (le_refl (two*E))
  have late := GaussianBinetSecondFrequencySchedule.early_precision (Γ := Γ) p D K
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hE : Γ ⊢[PRAAx] le one E := le_trans hU late.andE₂
  have hEtwo : Γ ⊢[PRAAx] le two E := by
    let t := index p D K
    have ht : Γ ⊢[PRAAx] le (num 4) t := le_add_left _ _
    have choose : Γ ⊢[PRAAx] le two (num 8*t) := by ipra_le 2+𝔞(t)*7+sl ht
    exact le_trans choose (le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _))
  have hL : Γ ⊢[PRAAx] le one L := GaussianBinetArctangentSineUniform.cutoff_positive q T K
  have hS : Γ ⊢[PRAAx] le one S := positive_product _ _ hD hL
  have angles := GaussianBinetSecondFrequencySchedule.count_budgets p q I E X Y D sign R T K hR
  have hAngle : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source X Y D sign A := angles.andE₁
  have cutData := certificates q D A T K E hD hEtwo hQ
  have hc : Γ ⊢[PRAAx] le one c := cutData.andE₁
  have hN : Γ ⊢[PRAAx] le one N := le_trans hc (le_of_lt cutData.andE₂.andE₁)
  have hMin : Γ ⊢[PRAAx] le (two*(S*E)) N :=
    le_trans (le_congr (by ipra_ring) (mul_comm (unit q) S) (mul_le_mul_right S hQ))
      (count_width_budget q D A T K)
  have pi := pi_bounds (Γ := Γ) u J T kMin
  have hPi : Γ ⊢[PRAAx] le (I*unit r) (unit k) :=
    le_trans (GaussianFastValueCut.query_budget I r) (unit_monotone pi.andE₁)
  have grid := mesh_bounds a D T v J k meshMin hT
  have hMesh : Γ ⊢[PRAAx] le meshMin M := grid.andE₂.andE₂.andE₂.andE₁
  have hM : Γ ⊢[PRAAx] le ((num 10*I+S)*T) M := le_trans (le_add_left _ _) hMesh
  have hP : Γ ⊢[PRAAx] le (unit (s+N)) M := le_trans (le_add_right _ _) hMesh
  have hm : Γ ⊢[PRAAx] le one M := le_trans (unit_positive (s+N)) hP
  have hLate : Γ ⊢[PRAAx] le q b := (frozen_bounds (Γ := Γ) p u T v J k M q).andE₁.andE₂
  have later := GaussianBinetSecondFrequencySchedule.laplace_clock_budget (Γ := Γ) p D L
  have origin := origin_bounds p D K I X hX
  let d := GaussianBinetSecondFormulaReduction.clock p X Y D sign K
  have hd : Γ ⊢[PRAAx] le p d :=
    GaussianNaturalScaleProductName.clock_later Bose p two (boseData X Y D sign K)
  have bose : Γ ⊢[PRAAx] distanceBounded (ap2 Bose d (boseData X Y D sign K)) f (num 9) U :=
    GaussianBinetBoseLateSchedule.observation p d T I v kMin meshMin q K X Y D sign h hT hI hd
      (GaussianBinetSecondFrequencySchedule.far_time_budget p D K) origin.andE₁
      (GaussianBinetSecondEarlySchedule.bose_tail_budget p D K) origin.andE₂
  have zRead : Γ ⊢[PRAAx] z ≐ qmul (fraction two one) (ap2 Bose d (boseData X Y D sign K)) :=
    (GaussianBinetSecondFormulaReduction.sample_at p X Y D sign K).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product two _)
  have first : Γ ⊢[PRAAx] distanceBounded z f' (num 18) U :=
    distance_congr zRead.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) (double_distance _ _ _ _ hU bose)
  have retiming := GaussianBinetSecondDecayRetiming.scheduled_prefix_distance q b k I M T X Y D sign A K
    hAngle hm h.andE₂ hLate
  have retimingBound : Γ ⊢[PRAAx] le ((two*(I*(T*(num 24+num 4*K*T))))*U) (one*unit q) :=
    le_congr (by ipra_ring) (one_mul _).eqSymm (GaussianBinetSecondEarlySchedule.atan_sum_budget p D K)
  have second : Γ ⊢[PRAAx] distanceBounded f' g' one U :=
    fit _ _ _ _ _ p (unit_positive q) retimingBound (double_distance _ _ _ _ (unit_positive q) retiming)
  have transposeBound : Γ ⊢[PRAAx] le ((I*(num 32*T*(T+one)))*U) (one*E) :=
    le_congr (by ipra_ring) (one_mul E).eqSymm (GaussianBinetSecondEarlySchedule.strip_sum_budget p D K)
  have third : Γ ⊢[PRAAx] distanceBounded g' x one U :=
    fit _ _ _ _ _ p hE transposeBound
      (GaussianBinetSecondWeightedSineTransposedPrefix.prefix_error q k I M T X Y D sign A K c E
        hAngle hm cutData.andE₂.andE₂.andE₁)
  have angularBound := GaussianBinetSecondErrorBudget.angular_budget p s I E S T
    (GaussianBinetSecondFrequencySchedule.angular_rounding_budget p q I E D R T K late.andE₁ hD hT hK)
    (GaussianBinetSecondEarlySchedule.sine_tail_budget p D K)
  have fourth : Γ ⊢[PRAAx] distanceBounded x m two U :=
    fit _ _ _ _ _ p (positive_product _ _ (unit_positive s) (unit_positive T)) angularBound
      (GaussianBinetSineKernelPrefix.prefix_error q k I M T X Y D sign A K E
        hAngle hS hN hE hMin hc angles.andE₂.andE₂.andE₂ hM hP)
  have kernelBound := GaussianBinetSecondErrorBudget.kernel_budget p r l I S
    (GaussianBinetSecondEarlySchedule.kernel_budget p D K)
    (GaussianBinetSecondFrequencySchedule.kernel_clock_budget p S) later.andE₂
  have fifth : Γ ⊢[PRAAx] distanceBounded m w (num 3) U :=
    fit _ _ _ _ _ p (GaussianBinetKernelFrozenIndependent.error_denominator_positive r l I hI) kernelBound
      (GaussianBinetFrozenKernelLaplace.sine_suffix_error s r l k I N X Y D sign A R L E
        hAngle hR hN hL hE hI hPi angles.andE₂.andE₂.andE₁)
  have laplaceBound := GaussianBinetSecondErrorBudget.laplace_budget p X D L E hX
    (GaussianBinetSecondEarlySchedule.frequency_cutoff_budget p D K) late.andE₂
  have sixth : Γ ⊢[PRAAx] distanceBounded y w (num 10) U :=
    fit _ _ _ _ _ p (GaussianBinetLaplaceFrequencySuffix.error_denominator_positive p p X L E hX hE) laplaceBound
      (GaussianBinetLaplaceFrequencySuffix.sine_suffix_error p p l N X Y D sign R L E
        hR hL hN later.andE₁ angles.andE₂.andE₁ hE)
  have left := distance_triangle_same z f' g' _ _ U hU first second
  have middle := distance_triangle_same g' x m _ _ U hU third fourth
  have right := distance_triangle_same m w y _ _ U hU fifth (distance_symmetric _ _ _ _ hU sixth)
  have out := distance_triangle_same z m y _ _ U hU
    (distance_triangle_same z g' m _ _ U hU left middle) right
  exact distance_symmetric z y _ U hU (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) out)

theorem improper_comparison (X Y D sign K : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) :
    Γ ⊢[PRAAx] rawDiagonal First Second (laplaceData X Y D sign) (secondData X Y D sign K) (num 35) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift K) := by
    simpa only [Fm.shift,Syn.shift,GaussianBinetBoseImproperName.subst_source] using h.shift
  simpa only [Syn.shift,subst_laplaceData,GaussianBinetSecondFormulaReduction.subst_data,PTm.subst_num] using
    observation_error (var 0) (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift K) hs

theorem equivalent (X Y D sign K z : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign K) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBinetStirlingRemainder.nameF Second
      (GaussianBinetStirlingRemainder.data X Y D sign z) (secondData X Y D sign K) :=
  GaussianBinetSecondFormulaReduction.identity_of_improper_comparison X Y D sign K (num 35) z h
    (improper_comparison X Y D sign K h)

theorem actual_second_Binet_formula_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent GaussianBinetStirlingRemainder.nameF Second
        (GaussianBinetStirlingRemainder.data (var 0) (var 1) (var 2) (var 3) (var 5))
        (secondData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (equivalent _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondFormula
