import IPRADerivations.Analysis.Gamma.NegativeAxis.Recurrence.GaussianGammaNegativeIntervalNamedInverseRecurrence
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalFrozenRate
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalNamedDerivative
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.NamedValues.GaussianGammaNegativeIntervalNamedCorrectionFactor

/-!
# The named derivative form of the inverse Gamma recurrence

At a common late rational offset, the inverse-factor product rule has
the original rational negative-Gamma derivative target. Uniform
comparison of the four named factors preserves this exact identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDerivativeRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianGammaNegativeIntervalNamedInverseRecurrence (terminalClock terminal_frozen_rate)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (terminalF terminalData terminal_source derivativeF derivativeData derivative_regular)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNameRingLaws (three)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "I" => GaussianGammaNegativeIntervalNamedInverseFactor.nameF
local notation "id" => GaussianGammaNegativeIntervalNamedInverseFactor.data
local notation "C" => GaussianGammaNegativeIntervalNamedCorrectionFactor.nameF
local notation "cd" => GaussianGammaNegativeIntervalNamedCorrectionFactor.data
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "NF" => GaussianGammaNegativeIntervalNamedDerivative.nameF
local notation "nd" => GaussianGammaNegativeIntervalNamedDerivative.data
local notation "RF" => GaussianGammaNegativeIntervalInverseRecurrence.targetF
local notation "rd" => GaussianGammaNegativeIntervalInverseRecurrence.targetData
local notation "DF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "dd" => GaussianGammaNegativeIntervalDerivativeTarget.data

def targetF (f : PR 2) : PR 2 :=
  addF (multiplyF (I f) (derivativeF f)) (multiplyF (C f) (G (terminalF f)))
def targetData (f : PR 2) (x E N : PTm n) : PTm n :=
  addData (multiplyData (I f) (derivativeF f) (id x E N) (derivativeData x))
    (multiplyData (C f) (G (terminalF f)) (cd x E N) (gd (terminalData x) one))

def productCost (F P : PR 2) (x y A : PTm n) : PTm n := U P y+(U F x+three)*A
def targetCost (f : PR 2) (x E N : PTm n) : PTm n :=
  productCost (I f) (derivativeF f) (id x E N) (derivativeData x) (num 5)+
    productCost (C f) (G (terminalF f)) (cd x E N) (gd (terminalData x) one) one

def comparisonCost (f : PR 2) (x E N : PTm n) : PTm n :=
  GaussianGammaNegativeIntervalNamedDerivative.productCost f x E N+targetCost f x E N

theorem target_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (targetF f) (targetData f x E N) :=
  add_fast _ _ _ _ (multiply_fast _ _ _ _
    (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N h) (derivative_regular f x E h))
    (multiply_fast _ _ _ _ (GaussianGammaNegativeIntervalNamedCorrectionFactor.name_regular f x E N h)
      (GaussianNamedGamma.name_regular _ _ _ (terminal_source f x E h)))

private theorem product_frozen_rate (F P H : PR 2) (x y u v A s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN P y) (hh : Γ ⊢[PRAAx] pointCN H v)
    (left : Γ ⊢[PRAAx] independentRate F constantF x u one (unit s))
    (right : Γ ⊢[PRAAx] independentRate P H y v A (unit s)) :
    Γ ⊢[PRAAx] independentRate (multiplyF F P) (multiplyF constantF H)
      (multiplyData F P x y) (multiplyData constantF H u v) (productCost F P x y A) (unit s) := by
  have hc := constant_regular (Γ := Γ) u
  have bound := (GaussianGammaNegativeIntervalExponentialFreeze.second_input F constantF x u s hf hc left).andE₂
  have un := unit_positive (Γ := Γ) s
  have rate := GaussianNamedMultiplyRate.independent_rate F P constantF H x y u v one (unit s) A (unit s)
    (U P y) (U F x+three) un un hf hg hc hh (all_samples_bounded P y hg) bound left right
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ un un) un
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedMultiplyRate.leadingNumerator,
      GaussianNamedMultiplyRate.leadingDenominator,productCost]; ipra_ring)) rate

theorem original_comparison_rate (f : PR 2) (s x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] independentRate (NF f) (targetF f) (nd f x E N) (targetData f x E N)
      (comparisonCost f x E N) (unit s) := by
  let R := GaussianGammaNegativeIntervalNamedInverseRecurrence.freezeClock f s x E N
  let S := GaussianGammaNegativeIntervalNamedTerminalFrozenRate.minimumClock f s x
  let J := GaussianGammaNegativeIntervalNamedCorrectionFactor.clock s E N
  let L := GaussianGammaNegativeIntervalNamedDerivative.freezeClock f s x E N
  let r := (R+S)+(J+L)
  let k := GaussianEulerNamedShiftInput.clock r
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let X := id x E N
  let Y := derivativeData x
  let U₀ := cd x E N
  let V := gd (terminalData x) one
  let i := GaussianGammaNegativeIntervalInverseRecurrence.inverse a b N
  let c := GaussianGammaNegativeIntervalInverseRecurrence.correctionFactor a b N
  let e := GaussianGammaDigammaNative.derivativeData (b+a) b
  let g := GaussianStirlingGammaLogarithm.gammaData (b+a) b
  let D := GaussianEulerLogarithmicImproperName.nameF
  have before := GaussianEulerNamedShiftInput.clock_later (Γ := Γ) r
  have hR : Γ ⊢[PRAAx] le R r := le_trans (le_add_right R S) (le_add_right (R+S) (J+L))
  have hS : Γ ⊢[PRAAx] le S r := le_trans (le_add_left S R) (le_add_right (R+S) (J+L))
  have hJ : Γ ⊢[PRAAx] le J k := le_trans (le_add_right J L) (le_trans (le_add_left (J+L) (R+S)) before)
  have hL : Γ ⊢[PRAAx] le L k := le_trans (le_add_left L J) (le_trans (le_add_left (J+L) (R+S)) before)
  have hI : Γ ⊢[PRAAx] le (GaussianGammaNegativeIntervalNamedInverseFactor.clock s E N) k :=
    le_trans (le_add_left _ _) (le_trans (le_add_left _ _) (le_trans hR before))
  have hG : Γ ⊢[PRAAx] le (terminalClock f s x) r := le_trans (le_add_right _ _) hR
  have domain := frozen_guard f k x E h
  have hi := GaussianGammaNegativeIntervalNamedInverseFactor.original_frozen_rate f s k x E N h hI
  have hc := GaussianGammaNegativeIntervalNamedCorrectionFactor.original_frozen_rate f s k x E N h hJ
  have he := GaussianGammaNegativeIntervalNamedTerminalFrozenRate.original_rate f s r x E h hS
  have hg := terminal_frozen_rate f s r x E h hG
  have left := product_frozen_rate (I f) (derivativeF f) D X Y i e (num 5) s
    (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N h)
    (derivative_regular f x E h) (GaussianGammaDigammaNative.derivative_regular _ _ (shifted_source a b domain)) hi he
  have right := product_frozen_rate (C f) (G (terminalF f)) gammaF U₀ V c g one s
    (GaussianGammaNegativeIntervalNamedCorrectionFactor.name_regular f x E N h)
    (GaussianNamedGamma.name_regular _ _ _ (terminal_source f x E h))
    (GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b domain)) hc hg
  have un := unit_positive (Γ := Γ) s
  have both := GaussianNamedAddRate.independent_rate (multiplyF (I f) (derivativeF f))
    (multiplyF (C f) (G (terminalF f))) (multiplyF constantF D) (multiplyF constantF gammaF)
    (multiplyData (I f) (derivativeF f) X Y) (multiplyData (C f) (G (terminalF f)) U₀ V)
    (multiplyData constantF D i e) (multiplyData constantF gammaF c g)
    (productCost (I f) (derivativeF f) X Y (num 5)) (unit s)
    (productCost (C f) (G (terminalF f)) U₀ V one) (unit s) un un left right
  have exactRate : Γ ⊢[PRAAx] independentRate (targetF f) RF (targetData f x E N) (rd a b N)
      (targetCost f x E N) (unit s) :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ un un) un
      (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedRateComposition.leadingNumerator,
        GaussianNamedRateComposition.leadingDenominator,targetCost]; ipra_ring)) both
  have main := GaussianGammaNegativeIntervalNamedDerivative.frozen_product_rate f s k x E N h hL
  have moved := GaussianNamedRateTransport.transport (NF f) DF (NF f) RF
    (nd f x E N) (dd a b N) (nd f x E N) (rd a b N)
    (GaussianGammaNegativeIntervalNamedDerivative.productCost f x E N) (unit s) un main
    (cross_refl _ _ (GaussianGammaNegativeIntervalNamedDerivative.name_regular f x E N h))
    (GaussianGammaNegativeIntervalInverseRecurrence.target_cross a b N domain)
  exact GaussianNamedRateComposition.same_denominator (NF f) RF (targetF f) (nd f x E N) (rd a b N) (targetData f x E N)
    (GaussianGammaNegativeIntervalNamedDerivative.productCost f x E N) (unit s) (targetCost f x E N) un moved
    (GaussianNamedRateComposition.symmetric _ _ _ _ (targetCost f x E N) (unit s) un exactRate)

private theorem subst_namedDerivativeData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (nd f x E N) = nd f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [GaussianGammaNegativeIntervalNamedDerivative.data,GaussianGammaNegativeIntervalNamedGamma.actualData,
    GaussianGammaNegativeIntervalNamedGamma.signedData,GaussianGammaFiniteApproximantName.exponentialInputData]

private theorem subst_targetData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (targetData f x E N) = targetData f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [targetData,one]

private theorem subst_comparisonCost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (comparisonCost f x E N) = comparisonCost f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [comparisonCost,targetCost,productCost,GaussianGammaNegativeIntervalNamedDerivative.productCost,
    GaussianGammaNegativeIntervalNamedGamma.actualData,GaussianGammaNegativeIntervalNamedGamma.signedData,
    GaussianGammaFiniteApproximantName.exponentialInputData,three,one,two]

private theorem comparison_at (f : PR 2) (p x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (NF f) p (nd f x E N)) (ap2 (targetF f) p (targetData f x E N))
      (comparisonCost f x E N+two) (unit p) := by
  have u := unit_positive (Γ := Γ) p
  have d := diagonal_rate (NF f) (targetF f) (nd f x E N) (targetData f x E N)
    (comparisonCost f x E N) (unit p) p u (original_comparison_rate f p x E N h)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ u u) u (le_of_eq_add (d := zero) (by ipra_ring)) d

theorem original_target_cross (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] crossEquivalent (NF f) (targetF f) (nd f x E N) (targetData f x E N) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (comparisonCost f x E N+two)
    (GaussianGammaNegativeIntervalNamedDerivative.name_regular f x E N h) (target_regular f x E N h) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source f (sh x) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_namedDerivativeData,subst_targetData,
    subst_comparisonCost,LeanProofs.IPRA.PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
    sh,Syn.shift] using comparison_at f (var 0) (sh x) (sh E) (sh N) h'

theorem actual_named_negative_Gamma_derivative_inverse_target_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ crossEquivalent (NF f) (targetF f)
        (nd f (var 0) (var 1) (var 2)) (targetData f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_target_cross f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDerivativeRecurrence
