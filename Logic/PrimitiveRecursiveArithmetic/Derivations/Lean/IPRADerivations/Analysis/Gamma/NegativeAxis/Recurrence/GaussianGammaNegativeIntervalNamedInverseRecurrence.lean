import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedInverseFactor
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedGamma
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalInput
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeEncoding
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap

/-!
# The inverse Gamma recurrence for named negative offsets

The same late offset sample determines the rational negative argument,
its inverse factor and its positive terminal argument. The folded C24
recurrence at this sample transports through the three uniform rates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse liftedF liftedData)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular rateFactor)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (terminalF terminalData terminal_source terminal_rational_at)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl cross_symm)
open GaussianNameRingLaws (three)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (arg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "I" => GaussianGammaNegativeIntervalNamedInverseFactor.nameF
local notation "id" => GaussianGammaNegativeIntervalNamedInverseFactor.data
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "gp" => GaussianStirlingGammaLogarithm.gammaData
local notation "ng" => GaussianGammaNegativeIntervalNative.data

def terminalClock (f : PR 2) (s x : PTm n) : PTm n :=
  GaussianNamedRightHalfPlane.threshold one+
    succ (GaussianGammaHalfPlaneInputContinuity.modulus s (GaussianNamedRightHalfPlane.radius (terminalF f) (terminalData x)) (two*one))

def freezeClock (f : PR 2) (s x E N : PTm n) : PTm n :=
  terminalClock f s x+(GaussianGammaNegativeIntervalNamedLog.clock s E N+
    GaussianGammaNegativeIntervalNamedInverseFactor.clock s E N)

def productF (f : PR 2) : PR 2 := multiplyF (I f) (G (terminalF f))
def productData (f : PR 2) (x E N : PTm n) : PTm n :=
  multiplyData (I f) (G (terminalF f)) (id x E N) (gd (terminalData x) one)

def comparisonCost (f : PR 2) (x E N : PTm n) : PTm n :=
  rateFactor f x E N+(U (G (terminalF f)) (gd (terminalData x) one)+(U (I f) (id x E N)+three))

theorem terminal_late_input (f : PR 2) (s r x E : PTm n) (h : Γ ⊢[PRAAx] source f x E)
    (hr : Γ ⊢[PRAAx] le (terminalClock f s x) r) :
    Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input (terminalF f) s r (terminalData x) one :=
  .andI (terminal_source f x E h)
    (.andI (le_trans (le_add_right _ _) hr) (le_trans (le_add_left _ _) hr))

theorem terminal_frozen_rate (f : PR 2) (s r x E : PTm n) (h : Γ ⊢[PRAAx] source f x E)
    (hr : Γ ⊢[PRAAx] le (terminalClock f s x) r) : Γ ⊢[PRAAx]
    let k := GaussianEulerNamedShiftInput.clock r
    independentRate (G (terminalF f)) gammaF (gd (terminalData x) one)
      (gp (sampleDenominator f k x+sampleNumerator f k x) (sampleDenominator f k x)) one (unit s) := by
  let F := terminalF f
  let X := terminalData x
  let q := ap2 F r X
  let k := GaussianEulerNamedShiftInput.clock r
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let R := GaussianNamedRightHalfPlane.radius F X
  let left := GaussianNamedGammaLateInput.encodedData F r X one
  let right := gp (b+a) b
  have hl := terminal_late_input f s r x E h hr
  have src := GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source F s r X one hl)
  have rr := GaussianStirlingGammaLogarithm.gamma_source (b+a) b (shifted_source a b (frozen_guard f k x E h))
  have qeq : Γ ⊢[PRAAx] q ≐ ofGaussian (arg (b+a)) b := terminal_rational_at f r x E h
  have raw := GaussianGammaNamedPoleFreeEncoding.raw_source_of_fraction q (arg (b+a)) (b+a) b one b rr qeq
  have overlap := GaussianGammaRadiusOverlap.original_Gamma_overlap (rawGaussian q) R (b+a) (rawDen q)
    one (two*one) one b src raw
  have encoded := GaussianGammaNamedPoleFreeEncoding.raw_gamma_cross q (arg (b+a)) (b+a) b b rr qeq
  have eq : Γ ⊢[PRAAx] crossEquivalent gammaF gammaF left right :=
    cross_trans _ _ _ _ _ _ overlap encoded
  exact GaussianNamedRateTransport.transport (G F) gammaF (G F) gammaF (gd X one) left (gd X one) right
    one (unit s) (unit_positive s) (GaussianNamedGammaLateInput.original_independent_rate F s r X one hl)
    (cross_refl _ _ (GaussianNamedGamma.name_regular _ _ _ hl.andE₁)) (cross_symm _ _ _ _ eq)

theorem product_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (productF f) (productData f x E N) :=
  multiply_fast _ _ _ _ (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N h)
    (GaussianNamedGamma.name_regular _ _ _ (terminal_source f x E h))

theorem original_comparison_rate (f : PR 2) (s x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] independentRate (actualF f) (productF f) (actualData f x E N) (productData f x E N)
      (comparisonCost f x E N) (unit s) := by
  let R := terminalClock f s x
  let L := GaussianGammaNegativeIntervalNamedLog.clock s E N
  let J := GaussianGammaNegativeIntervalNamedInverseFactor.clock s E N
  let r := freezeClock f s x E N
  let k := GaussianEulerNamedShiftInput.clock r
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let X := id x E N
  let F := G (terminalF f)
  let Y := gd (terminalData x) one
  let C := inverse a b N
  let Z := gp (b+a) b
  let V := U F Y
  let W := U (I f) X+three
  let K := rateFactor f x E N
  have br : Γ ⊢[PRAAx] le R r := le_add_right R (L+J)
  have bk : Γ ⊢[PRAAx] le r k := GaussianEulerNamedShiftInput.clock_later r
  have bl : Γ ⊢[PRAAx] le L k := le_trans (le_add_right L J) (le_trans (le_add_left (L+J) R) bk)
  have bj : Γ ⊢[PRAAx] le J k := le_trans (le_add_left J L) (le_trans (le_add_left (L+J) R) bk)
  have domain := frozen_guard f k x E h
  have hI := GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N h
  have hF := GaussianNamedGamma.name_regular _ _ _ (terminal_source f x E h)
  have hC := constant_regular (Γ := Γ) C
  have hZ := GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b domain)
  have hi := GaussianGammaNegativeIntervalNamedInverseFactor.original_frozen_rate f s k x E N h bj
  have ht := terminal_frozen_rate f s r x E h br
  have bound := (GaussianGammaNegativeIntervalExponentialFreeze.second_input (I f) constantF X C s hI hC hi).andE₂
  have un := unit_positive (Γ := Γ) s
  have rp := GaussianNamedMultiplyRate.independent_rate (I f) F constantF gammaF X Y C Z
    one (unit s) one (unit s) V W un un hI hF hC hZ (all_samples_bounded F Y hF) bound hi ht
  have prodRate : Γ ⊢[PRAAx] independentRate (productF f) liftedF (productData f x E N) (liftedData a b N) (V+W) (unit s) :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
      (positive_product _ _ un un) un
      (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedMultiplyRate.leadingNumerator, GaussianNamedMultiplyRate.leadingDenominator]; ipra_ring)) rp
  have native := GaussianGammaNegativeIntervalNamedGamma.actual_frozen_rate f s k x E N h bl
  have base := GaussianNamedRateTransport.transport (actualF f) gammaF (actualF f) liftedF
    (actualData f x E N) (ng a b N) (actualData f x E N) (liftedData a b N) K (unit s) un native
    (cross_refl _ _ (actual_regular f x E N h))
    (cross_symm _ _ _ _ (GaussianGammaNegativeIntervalInverseRecurrence.original_inverse_product a b N domain))
  exact GaussianNamedRateComposition.same_denominator (actualF f) liftedF (productF f) (actualData f x E N)
    (liftedData a b N) (productData f x E N) K (unit s) (V+W) un base
    (GaussianNamedRateComposition.symmetric (productF f) liftedF (productData f x E N) (liftedData a b N) (V+W) (unit s) un prodRate)

private theorem subst_actualData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (actualData f x E N) = actualData f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [actualData,GaussianGammaNegativeIntervalNamedGamma.signedData,GaussianGammaFiniteApproximantName.exponentialInputData]

private theorem subst_comparisonCost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (comparisonCost f x E N) = comparisonCost f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [comparisonCost,rateFactor,three,one,two]

private theorem comparison_at (f : PR 2) (p x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (actualF f) p (actualData f x E N)) (ap2 (productF f) p (productData f x E N))
      (comparisonCost f x E N+two) (unit p) := by
  have u := unit_positive (Γ := Γ) p
  have d := diagonal_rate (actualF f) (productF f) (actualData f x E N) (productData f x E N)
    (comparisonCost f x E N) (unit p) p u (original_comparison_rate f p x E N h)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ u u) u (le_of_eq_add (d := zero) (by ipra_ring)) d

theorem original_inverse_product (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] crossEquivalent (actualF f) (productF f) (actualData f x E N) (productData f x E N) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (comparisonCost f x E N+two)
    (actual_regular f x E N h) (product_regular f x E N h) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source f (sh x) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_actualData,subst_comparisonCost,
    productData,GaussianNameArithmetic.subst_multiplyData,GaussianNamedGamma.subst_data,
    GaussianNamedUnitIntervalRationalLift.subst_data,GaussianEulerNamedShiftInput.subst_shiftData,
    LeanProofs.IPRA.PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,sh,Syn.shift] using
    comparison_at f (var 0) (sh x) (sh E) (sh N) h'

theorem actual_named_negative_Gamma_inverse_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ crossEquivalent (actualF f) (productF f)
        (actualData f (var 0) (var 1) (var 2)) (productData f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_inverse_product f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseRecurrence
