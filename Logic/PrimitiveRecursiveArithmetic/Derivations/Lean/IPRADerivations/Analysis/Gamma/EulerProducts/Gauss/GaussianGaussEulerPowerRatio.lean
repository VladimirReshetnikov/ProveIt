import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationPowerRate
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerCutoff
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift

/-!
# Exact Gauss power ratio at the two Euler cutoffs

Multiplying the actual ratio power by the exponential of the
logarithm of the upper cutoff times the common exponent restores
the exponential at the lower cutoff. Both logarithms are the
original Gamma mesh names, and the ratio uses its original
positive-rational logarithm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerPowerRatio

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (logF log_regular exponential_input exponentialInputData)
open GaussianGammaGaussEulerHeads (cutoff)
open GaussianGaussMultiplicationPowerRate (multiplier amplification rowLogData powerF powerData row_power_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_negative add_commutative add_associative
  zeroF zero_fast add_zero distributive)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (differenceF differenceData original_logarithm_difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "ratioLogF" => GaussianPositiveRationalLogarithm.logF
local notation "ratioLogData" => GaussianPositiveRationalLogarithm.data

private theorem zeros_at (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let X := Syn.shift (Syn.shift x)
  let Y := Syn.shift (Syn.shift y)
  have hx := GaussianNameRingLaws.zero_at (Γ := Δ) (var 0) X
  have hy := GaussianNameRingLaws.zero_at (Γ := Δ) (var 0) Y
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (hx.eqTrans hy.eqSymm) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.point_at zeroF X (var 1) (var 0) (zero_fast X))

theorem restore_log (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] crossEquivalent (addF ratioLogF logF) logF (addData (ratioLogData N L) L) N := by
  let G := negativeF logF
  let y := negativeData L
  let D := ratioLogData N L
  let C := differenceData N L
  have hn := log_regular (Γ := Γ) N hN
  have hl := log_regular (Γ := Γ) L hL
  have hneg := negative_fast logF L hl
  have hratio := GaussianPositiveRationalLogarithm.name_regular N L (.andI hN hL)
  have hdiff : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN differenceF C := add_fast logF G N y hn hneg
  have first := add_cross ratioLogF differenceF logF logF D C L L hratio hdiff hl hl
    (original_logarithm_difference N L (.andI hN hL)) (cross_refl logF L hl)
  have reorder := add_associative logF G logF N y L hn hneg hl
  have inv := cross_trans _ _ _ _ _ _ (add_commutative G logF y L hneg hl) (add_negative logF L hl)
  have replace := add_cross logF logF (addF G logF) zeroF N N (addData y L) L hn hn
    (add_fast G logF y L hneg hl) (zero_fast L) (cross_refl logF N hn) inv
  have zeroAt := zeros_at (Γ := Γ) L N
  have last := add_cross logF logF zeroF zeroF N N L N hn hn (zero_fast L) (zero_fast N)
    (cross_refl logF N hn) zeroAt
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ reorder
    (cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ last (GaussianNameRingLaws.add_zero logF N hn))))

def fixedExponentF : PR 2 := multiplyF constantF logF
def fixedExponentData (c N : PTm n) : PTm n := multiplyData constantF logF c N
def fixedPowerF : PR 2 := GaussianRadiusExponentialName.nameF fixedExponentF
def fixedPowerData (c N : PTm n) : PTm n := exponentialInputData fixedExponentF (fixedExponentData c N)

theorem fixed_exponent_regular (c N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN fixedExponentF (fixedExponentData c N) :=
  multiply_fast constantF logF c N (constant_regular c) (log_regular N hN)

private theorem same_input (f : PR 2) (x y : PTm n)
    (hx : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x)
    (hy : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f y) (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] crossEquivalent f f x y := by
  apply GaussianNameConjugation.equal_samples_cross f f x y hx hy
  refine .allI ?_
  have hh : Γ.map Fm.shift ⊢[PRAAx] Syn.shift x ≐ Syn.shift y := by simpa [Fm.shift,Syn.shift] using h.shift
  exact congrAp2 f (.eqRefl _) hh

theorem ratio_power_restore (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF powerF fixedPowerF) fixedPowerF
      (multiplyData powerF fixedPowerF (powerData z R B m (rowLogData m N)) (fixedPowerData (multiplier z B m) (cutoff m N)))
      (fixedPowerData (multiplier z B m) N) := by
  let L := cutoff m N
  let c := multiplier z B m
  let D := rowLogData m N
  let E := GaussianGaussMultiplicationPowerRate.exponentF
  let X := GaussianGaussMultiplicationPowerRate.exponentData z R B m D
  let Y := fixedExponentData c L
  let Z := fixedExponentData c N
  let F := multiplyF constantF ratioLogF
  let A := multiplyData constantF ratioLogF c D
  have hL := le_trans hN (GaussianGaussEulerCutoff.scaled_cutoff_later m N hm)
  have hn := log_regular (Γ := Γ) N hN
  have hl := log_regular (Γ := Γ) L hL
  have hC := constant_regular (Γ := Γ) c
  have hr := GaussianGaussMultiplicationPowerRate.row_log_regular m N hm hN
  have hex := row_power_input z R B m N hm hN hB hz
  have hy := fixed_exponent_regular c L hL
  have hz' := fixed_exponent_regular c N hN
  have ordinary := GaussianBoundedConstantProductName.ordinary_product_identity ratioLogF (amplification R m) c D
    (.andI hr (GaussianGaussMultiplicationPowerRate.multiplier_bound z R B m hm hB hz))
  have sum := add_cross E F fixedExponentF fixedExponentF X A Y Y hex.andE₁
    (multiply_fast constantF ratioLogF c D hC hr) hy hy ordinary (cross_refl _ _ hy)
  have same : Γ ⊢[PRAAx] D ≐ ratioLogData N L := by
    have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (ratioLogData (var 0) (var 1) : PTm 2)
      (σ := ![N,GaussianGaussMultiplicationLogarithm.top m N]) (σ' := ![N,L])
      (fun i => by fin_cases i; exact .eqRefl _; exact GaussianGaussEulerCutoff.scaled_log_cutoff m N hm)
    simpa [rowLogData,D] using e
  have hd' := GaussianPositiveRationalLogarithm.name_regular N L (.andI hN hL)
  have hd := same_input ratioLogF D (ratioLogData N L) hr hd' same
  have restored : Γ ⊢[PRAAx] crossEquivalent (addF ratioLogF logF) logF (addData D L) N := cross_trans _ _ _ _ _ _
    (add_cross ratioLogF ratioLogF logF logF D (ratioLogData N L) L L hr
      hd' hl hl hd (cross_refl _ _ hl))
    (restore_log N L hN hL)
  have distribute := distributive constantF ratioLogF logF c D L hC hr hl
  have lifted := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (addF ratioLogF logF) logF
    c c (addData D L) N hC hC (add_fast _ _ _ _ hr hl) hn (cross_refl _ _ hC) restored
  have exponent : Γ ⊢[PRAAx] crossEquivalent (addF E fixedExponentF) fixedExponentF (addData X Y) Z :=
    cross_trans _ _ _ _ _ _ sum (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ distribute) lifted)
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent E fixedExponentF fixedExponentF
    (GaussianGaussMultiplicationPowerRate.radius R m) (GaussianNameBounds.U fixedExponentF Y)
    (GaussianNameBounds.U fixedExponentF Z) X Y Z hex (exponential_input _ _ hy) (exponential_input _ _ hz') exponent

theorem actual_Gauss_Euler_power_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le one (var 4) ⟶ le one (var 2) ⟶
      ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      crossEquivalent (multiplyF powerF fixedPowerF) fixedPowerF
        (multiplyData powerF fixedPowerF (powerData (var 0) (var 1) (var 2) (var 3) (rowLogData (var 3) (var 4)))
          (fixedPowerData (multiplier (var 0) (var 2) (var 3)) (cutoff (var 3) (var 4))))
        (fixedPowerData (multiplier (var 0) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (ratio_power_restore _ _ _ _ _ Prf.hyp1.wk.wk
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerPowerRatio
