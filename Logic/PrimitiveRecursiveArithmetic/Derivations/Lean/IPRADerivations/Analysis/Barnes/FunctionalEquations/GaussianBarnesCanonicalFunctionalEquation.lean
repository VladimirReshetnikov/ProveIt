import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalFiniteGaussRate
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalShiftChart
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# The original Barnes functional equation on Gaussian rational inputs

At one common late cutoff use both literal Barnes truncations and the
original Euler approximation of reciprocal Gamma. The two errors from
the exact finite identity tend to zero under one primitive-recursive
schedule. The resulting cleared functional equation includes poles.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFunctionalEquation

open_ipra
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalFiniteGaussRate (targetF targetData remainderGain leftGain rightGain)
open GaussianBarnesCanonicalValue (nameF data regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerHeadLower (translated)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedRateComposition (symmetric same_denominator_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "L" => GaussianBarnesCanonicalFiniteGaussIdentity.leftF
local notation "F" => GaussianBarnesCanonicalFiniteGaussIdentity.rightF
local notation "ld" => GaussianBarnesCanonicalFiniteGaussIdentity.leftData
local notation "fd" => GaussianBarnesCanonicalFiniteGaussIdentity.rightData
local notation "cut" => GaussianBarnesCanonicalUniformCutoff.cutoff
local notation "gain" => GaussianGammaEulerApproximationName.rate
local notation "need" => GaussianGammaPerturbationExponent.numerator

def cutoffIndex (R p : PTm n) : PTm n :=
  let S := R+one
  cut R p+cut S p+(two*S+need S)+(gain S+remainderGain S S+S)*unit p

def comparisonCost (z R B : PTm n) : PTm n := leftGain z (R+one) B+rightGain z R (R+one) B (R+one)

theorem comparison_slack (z R B p q m : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    slack (qsub (ap2 targetF p (targetData z (R+one) B)) (ap2 nameF q (data z R B)))
      (unit p+unit q) (unit p*unit q) (comparisonCost z R B) m := by
  let S := R+one
  let w := translated z B one
  let N := cutoffIndex R m
  let K := succ N
  let U := unit m
  let c := cut R m
  let d := cut S m
  let a := gain S
  let b := remainderGain S S
  let j := need S
  have hK := zero_lt_succ (Γ := Γ) N
  have later : Γ ⊢[PRAAx] le (c+d+(two*S+j)+(a+b+S)*U) K := le_succ_self N
  have hC : Γ ⊢[PRAAx] le c K := by ipra_le sl later+𝔞 d+2*𝔞 S+𝔞 j+(𝔞 a+𝔞 b+𝔞 S)*𝔞 U
  have hD : Γ ⊢[PRAAx] le d K := by ipra_le sl later+𝔞 c+2*𝔞 S+𝔞 j+(𝔞 a+𝔞 b+𝔞 S)*𝔞 U
  have hS : Γ ⊢[PRAAx] le (two*S) K := by ipra_le sl later+𝔞 c+𝔞 d+𝔞 j+(𝔞 a+𝔞 b+𝔞 S)*𝔞 U
  have hJ : Γ ⊢[PRAAx] le j K := by ipra_le sl later+𝔞 c+𝔞 d+2*𝔞 S+(𝔞 a+𝔞 b+𝔞 S)*𝔞 U
  have hA : Γ ⊢[PRAAx] le (a*U) K := by ipra_le sl later+𝔞 c+𝔞 d+2*𝔞 S+𝔞 j+(𝔞 b+𝔞 S)*𝔞 U
  have hB : Γ ⊢[PRAAx] le (b*U) K := by ipra_le sl later+𝔞 c+𝔞 d+2*𝔞 S+𝔞 j+(𝔞 a+𝔞 S)*𝔞 U
  have hP : Γ ⊢[PRAAx] le (S*U) K := by ipra_le sl later+𝔞 c+𝔞 d+2*𝔞 S+𝔞 j+(𝔞 a+𝔞 b)*𝔞 U
  have transBound := GaussianBarnesCanonicalShiftChart.translated_bound z R B h.andE₂
  have hw : Γ ⊢[PRAAx] source w S B := .andI h.andE₁ transBound
  have hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source w S B K := .andI h.andE₁ (.andI hK (.andI transBound hS))
  have mid := GaussianBarnesCanonicalShiftChart.half_shift_bound z R B h.andE₁ h.andE₂
  have gs : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source w S B K :=
    .andI (.andI (le_add_left one R) hw) (.andI hS hJ)
  let x := ld z S B K
  let y := fd z R S B K
  let X := targetData z S B
  let Y := data z R B
  let gL := leftGain z S B
  let gR := rightGain z R S B S
  have u := unit_positive (Γ := Γ) m
  have l := GaussianBarnesCanonicalFiniteGaussRate.left_rate z S B K m hK gs hD hA
  have r := GaussianBarnesCanonicalFiniteGaussRate.right_rate z R S B S K m h hs mid hC hB hP
  have e := GaussianBarnesCanonicalFiniteGaussIdentity.original_finite_recurrence z R S B N h hw hS
  have rg := GaussianNameArithmetic.multiply_fast nameF GaussianGammaC7Name.nameF _ _ (regular w S B hw)
    (GaussianGammaC7Name.name_regular w S B gs.andE₁)
  have l' := GaussianNamedRateTransport.transport L targetF F targetF x X y X gL U u l
    (cross_symm _ _ _ _ e) (cross_refl _ _ rg)
  have joined := same_denominator_at targetF F nameF X y Y gL U gR p q u
    (symmetric F targetF y X gL U u l') r
  change Γ ⊢[PRAAx] distanceBounded (ap2 targetF p X) (ap2 nameF q Y)
    ((unit p+unit q)*U+(gL+gR)*(unit p*unit q)) ((unit p*unit q)*U)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) joined

theorem comparison_at (z R B p q : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 targetF p (targetData z (R+one) B)) (ap2 nameF q (data z R B)) (unit p+unit q) (unit p*unit q) :=
  slack_removal_at _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (comparison_slack z R B p q _ h)

theorem functional_equation (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent targetF nameF (targetData z (R+one) B) (data z R B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  simpa [crossEquivalent,GaussianBarnesCanonicalFiniteGaussRate.targetData,Syn.shift,sh,Δ,one] using
    comparison_at (sh z) (sh R) (sh B) (var 1) (var 0) hs

theorem actual_Barnes_canonical_functional_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let z := var 0
     let R := var 1
     let B := var 2
     source z R B ⟶ crossEquivalent targetF nameF (targetData z (R+one) B) (data z R B)) :=
  closeUniv 3 (.impI (functional_equation _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFunctionalEquation
