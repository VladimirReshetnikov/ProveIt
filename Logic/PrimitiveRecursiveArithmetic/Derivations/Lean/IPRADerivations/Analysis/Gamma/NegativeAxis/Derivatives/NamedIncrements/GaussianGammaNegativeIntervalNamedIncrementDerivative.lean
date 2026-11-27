import IPRADerivations.Analysis.Gamma.NegativeAxis.Recurrence.GaussianGammaNegativeIntervalNamedDerivativeRecurrence
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.NamedIncrements.GaussianGammaNegativeIntervalNamedInverseDerivative
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.NamedIncrements.GaussianGammaNegativeIntervalNamedInverseFactorIncrement
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.NamedIncrements.GaussianGammaNegativeIntervalNamedIncrementSetup
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Named.GaussianNamedEulerUnitTimeMargin
import IPRADerivations.Analysis.Names.Differences.GaussianNamedIncrementProductRule

/-!
# Derivative of the original Gamma on a named negative interval

The original named increment is used throughout. Apply the exact
product rule to the inverse shift factor and positive Euler terminal
value, then identify the resulting derivative with Gamma times the
original shifted digamma. The bound is uniform in the increment's
apartness certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedIncrementDerivative

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular)
open GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient (offsetQuotientF offsetQuotientData nativeQuotientF nativeQuotientData)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (source derivativeF derivativeData terminalF terminalData endpoint_source)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (multiply_commutative)
open GaussianNamedGammaSmallIncrementInput (sumData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedRateComposition (symmetric)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianGammaNegativeIntervalNamedInverseFactor.nameF
local notation "id" => GaussianGammaNegativeIntervalNamedInverseFactor.data
local notation "C" => GaussianGammaNegativeIntervalNamedCorrectionFactor.nameF
local notation "cd" => GaussianGammaNegativeIntervalNamedCorrectionFactor.data
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "Q" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data
local notation "TF" => GaussianGammaNegativeIntervalNamedDerivativeRecurrence.targetF
local notation "td" => GaussianGammaNegativeIntervalNamedDerivativeRecurrence.targetData
local notation "NF" => GaussianGammaNegativeIntervalNamedDerivative.nameF
local notation "nd" => GaussianGammaNegativeIntervalNamedDerivative.data
local notation "gainI" => GaussianGammaNegativeIntervalNamedInverseFactorIncrement.gain
local notation "gainD" => GaussianGammaNegativeIntervalNamedInverseDerivative.gain

def factorCost (f : PR 2) (x W N : PTm n) : PTm n :=
  U (derivativeF f) (derivativeData x)*gainI W N+W*W

def correctionCost (f : PR 2) (x W N : PTm n) : PTm n :=
  U (G (terminalF f)) (gd (terminalData x) one)*gainD W N

def cost (f : PR 2) (x W N : PTm n) : PTm n := factorCost f x W N+correctionCost f x W N

private theorem product_rate (F J H K : PR 2) (x y u v A L B M R : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN J y)
    (hh : Γ ⊢[PRAAx] pointCN H u) (hk : Γ ⊢[PRAAx] pointCN K v)
    (hM : Γ ⊢[PRAAx] sampleBound J y M) (hR : Γ ⊢[PRAAx] sampleBound H u R)
    (ef : Γ ⊢[PRAAx] independentRate F H x u A B) (eg : Γ ⊢[PRAAx] independentRate J K y v L B) :
    Γ ⊢[PRAAx] independentRate (multiplyF F J) (multiplyF H K) (multiplyData F J x y) (multiplyData H K u v)
      (M*A+R*L) B :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hB hB) hB
    (le_of_eq_add (d := zero) (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring))
    (GaussianNamedMultiplyRate.independent_rate F J H K x y u v A B L B M R hB hB hf hg hh hk hM hR ef eg)

theorem original_rate (f K : PR 2) (p x z E N a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x z E a) :
    Γ ⊢[PRAAx] independentRate (offsetQuotientF f K) (NF f)
      (offsetQuotientData f K x z (two*E) (two*E) N a) (nd f x (two*E) N) (cost f x (two*E) N) (unit p) := by
  let W := two*E
  let g := GaussianNamedGammaSmallIncrementInput.sumF f K
  let y := sumData x z
  let I₀ := I f
  let I₁ := I g
  let i₀ := id x W N
  let i₁ := id y W N
  let G₀ := G (terminalF f)
  let G₁ := G (terminalF g)
  let g₀ := gd (terminalData x) one
  let g₁ := gd (terminalData y) one
  let T := derivativeF f
  let t := derivativeData x
  let J := C f
  let j := cd x W N
  let QG := Q G₁ G₀ K
  let qg := qd G₁ G₀ K g₁ g₀ z a
  let QI := Q I₁ I₀ K
  let qi := qd I₁ I₀ K i₁ i₀ z a
  let B := unit p
  have hB := unit_positive (Γ := Γ) p
  have hf := GaussianNamedEulerUnitTimeMargin.double f x E hs.andE₁
  have hg := endpoint_source f K p x z E a hs
  have hk := hs.andE₂.andE₂.andE₁
  have he := GaussianGammaNegativeIntervalNamedIncrementSetup.increment_cross f K x z hs.andE₁.andE₁ hk.andE₁
  have small := GaussianGammaNegativeIntervalNamedIncrementSetup.small_from_source f K p x z E a hs
  have i0reg := GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x W N hf
  have i1reg := GaussianGammaNegativeIntervalNamedInverseFactor.name_regular g y W N hg
  have jreg := GaussianGammaNegativeIntervalNamedCorrectionFactor.name_regular f x W N hf
  have source₀ := GaussianGammaNegativeIntervalNamedTerminalDerivative.terminal_source f x W hf
  have source₁ := GaussianGammaNegativeIntervalNamedTerminalDerivative.terminal_source g y W hg
  have g0reg : Γ ⊢[PRAAx] pointCN G₀ g₀ := GaussianNamedGamma.name_regular _ _ _ source₀
  have g1reg : Γ ⊢[PRAAx] pointCN G₁ g₁ := GaussianNamedGamma.name_regular _ _ _ source₁
  have treg : Γ ⊢[PRAAx] pointCN T t := GaussianNamedEulerLogarithmicImproper.name_regular _ _ _ _ source₀
  have qgreg : Γ ⊢[PRAAx] pointCN QG qg :=
    GaussianNamedIncrementDifferenceQuotient.name_regular G₁ G₀ K g₁ g₀ z a (.andI g1reg (.andI g0reg hk))
  have qireg : Γ ⊢[PRAAx] pointCN QI qi :=
    GaussianNamedIncrementDifferenceQuotient.name_regular I₁ I₀ K i₁ i₀ z a (.andI i1reg (.andI i0reg hk))
  have hG : Γ ⊢[PRAAx] independentRate QG T qg t one B :=
    GaussianGammaNegativeIntervalNamedTerminalDerivative.original_rate f K p x z E a hs
  have hI : Γ ⊢[PRAAx] independentRate QI J qi j (gainD W N) B :=
    GaussianGammaNegativeIntervalNamedInverseDerivative.original_rate f g K p x y z W N a
      (.andI hf (.andI hg (.andI hk (.andI he small))))
  have iMove := GaussianGammaNegativeIntervalNamedInverseFactorIncrement.original_rate f g K p x y z W N hf hg he small
  have boundI := GaussianGammaNegativeIntervalNamedInverseFactorIncrement.all_samples_bounded g y W N hg
  have first := product_rate I₀ T I₁ QG i₀ t i₁ qg (gainI W N) one B (U T t) (W*W) hB i0reg treg i1reg qgreg
    (all_samples_bounded T t treg) boundI iMove (symmetric QG T qg t one B hB hG)
  have firstRate := GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ (factorCost f x W N) B
    (by unfold factorCost; ipra_ring) (.eqRefl _) first
  have same := GaussianNamedRateRadius.weaken G₀ G₀ g₀ g₀ zero one zero B (le_refl _) hB
    (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianNamedAddRate.self_rate G₀ g₀ g0reg)
  have second := product_rate G₀ J G₀ QI g₀ j g₀ qi zero (gainD W N) B (U J j) (U G₀ g₀) hB g0reg jreg g0reg qireg
    (all_samples_bounded J j jreg) (all_samples_bounded G₀ g₀ g0reg) same (symmetric QI J qi j _ _ hB hI)
  have secondRate := GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ (correctionCost f x W N) B
    (by unfold correctionCost; ipra_ring) (.eqRefl _) second
  have secondReordered := GaussianNamedRateTransport.transport (multiplyF G₀ J) (multiplyF G₀ QI)
    (multiplyF J G₀) (multiplyF G₀ QI) (multiplyData G₀ J g₀ j) (multiplyData G₀ QI g₀ qi)
    (multiplyData J G₀ j g₀) (multiplyData G₀ QI g₀ qi) (correctionCost f x W N) B hB secondRate
    (multiply_commutative J G₀ j g₀ jreg g0reg)
    (cross_refl _ _ (GaussianNameArithmetic.multiply_fast _ _ _ _ g0reg qireg))
  have both := GaussianNamedAddRate.independent_rate (multiplyF I₀ T) (multiplyF J G₀)
    (multiplyF I₁ QG) (multiplyF G₀ QI) _ _ _ _ (factorCost f x W N) B (correctionCost f x W N) B hB hB
    firstRate secondReordered
  let R := GaussianNamedIncrementProductRule.rhsF I₁ I₀ G₁ G₀ K
  let r := GaussianNamedIncrementProductRule.rhsData I₁ I₀ G₁ G₀ K i₁ i₀ g₁ g₀ z a
  have right := GaussianNamedRateRadius.weaken (TF f) R (td f x W N) r _ _ (cost f x W N) B
    (positive_product _ _ hB hB) hB (le_of_eq_add (d := zero)
      (by unfold GaussianNamedAddRate.leadingNumerator cost; ipra_ring)) both
  have nativeLeft := GaussianNamedIncrementDifferenceQuotientProperness.proper (actualF g) (multiplyF I₁ G₁)
    (actualF f) (multiplyF I₀ G₀) K (actualData g y W N) (multiplyData I₁ G₁ i₁ g₁)
    (actualData f x W N) (multiplyData I₀ G₀ i₀ g₀) z a (actual_regular g y W N hg)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ i1reg g1reg) (actual_regular f x W N hf)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ i0reg g0reg) hk
    (GaussianGammaNegativeIntervalNamedInverseRecurrence.original_inverse_product g y W N hg)
    (GaussianGammaNegativeIntervalNamedInverseRecurrence.original_inverse_product f x W N hf)
  have split := GaussianNamedIncrementProductRule.product_rule I₁ I₀ G₁ G₀ K i₁ i₀ g₁ g₀ z a
    i1reg i0reg g1reg g0reg hk
  exact GaussianNamedRateTransport.transport R (TF f) (offsetQuotientF f K) (NF f)
    r (td f x W N) (offsetQuotientData f K x z W W N a) (nd f x W N) (cost f x W N) B hB
    (symmetric _ _ _ _ _ _ hB right) (cross_trans _ _ _ _ _ _ nativeLeft split)
    (GaussianGammaNegativeIntervalNamedDerivativeRecurrence.original_target_cross f x W N hf)


theorem native_rate (f K : PR 2) (p x z E N a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x z E a) :
    Γ ⊢[PRAAx] independentRate (nativeQuotientF f K) (NF f)
      (nativeQuotientData f K x z (two*E) (two*E) N a) (nd f x (two*E) N) (cost f x (two*E) N) (unit p) := by
  let W := two*E
  have hf := GaussianNamedEulerUnitTimeMargin.double f x E hs.andE₁
  have hg := endpoint_source f K p x z E a hs
  have hk := hs.andE₂.andE₂.andE₁
  have he := GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient.original_cross f K x z W W N a hf hg hk
  exact GaussianNamedRateTransport.transport (offsetQuotientF f K) (NF f) (nativeQuotientF f K) (NF f)
    (offsetQuotientData f K x z W W N a) (nd f x W N) (nativeQuotientData f K x z W W N a) (nd f x W N)
    (cost f x W N) (unit p) (unit_positive p) (original_rate f K p x z E N a hs)
    (GaussianNameEquivalence.cross_symm _ _ _ _ he)
    (cross_refl _ _ (GaussianGammaNegativeIntervalNamedDerivative.name_regular f x W N hf))

theorem actual_original_negative_interval_named_Gamma_derivative_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f K (var 0) (var 1) (var 2) (var 3) (var 5) ⟶
        independentRate (nativeQuotientF f K) (NF f)
          (nativeQuotientData f K (var 1) (var 2) (two*var 3) (two*var 3) (var 4) (var 5))
          (nd f (var 1) (two*var 3) (var 4)) (cost f (var 1) (two*var 3) (var 4)) (unit (var 0))) :=
  closeUniv 6 (.impI (native_rate f K _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedIncrementDerivative
