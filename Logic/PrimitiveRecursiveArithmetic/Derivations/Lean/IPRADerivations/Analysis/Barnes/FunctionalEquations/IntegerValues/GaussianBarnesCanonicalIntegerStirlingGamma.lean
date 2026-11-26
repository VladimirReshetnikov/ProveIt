import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.GaussianBarnesCanonicalIntegerLogarithm
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingCubicRate
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogShift
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Cubic Stirling comparison for the original factorial logarithm

The original `log Γ(N+1)` comes from the original logarithmic Gamma
increment at `N`. The checked shifted Stirling normalizer includes the
literal first correction `1/(12*N)` and has independent leading
error at most `1/N^3` for positive integers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerStirlingGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalIntegerLogarithm (factorialLogData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedDifferenceRate (self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianStirlingCubicCell (cube cube_positive)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData remainder_regular normalizationF normalizationData
  normalization_regular sumData logarithmic_cancellation)
open GaussianStirlingRationalTelescopers (upperValue)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "SF" => GaussianStirlingMultiplicativeAlgebra.sumF
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data

def normalization (N : PTm n) : PTm n := normalizationData N one zero
def correction (N : PTm n) : PTm n := upperValue N one
abbrev approximationF : PR 2 := addF H (addF constantF normalizationF)
def approximationData (N : PTm n) : PTm n := addData (hd N one) (addData (correction N) (normalization N))

theorem source (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] GaussianStirlingNames.source N one :=
  .andI hN (le_refl _)

theorem approximation_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN approximationF (approximationData N) :=
  add_fast _ _ _ _ (GaussianHarmonicLogarithmName.name_regular _ _ (source N hN))
    (add_fast _ _ _ _ (constant_regular _) (normalization_regular _ _ _ (source N hN)))

private theorem factorial_datum (N : PTm n) :
    Γ ⊢[PRAAx] factorialLogData N ≐ logGammaData (N+one) one := by
  have eq : Γ ⊢[PRAAx] succ N ≐ N+one := by ipra_ring
  simpa only [factorialLogData,GaussianStirlingGammaLogarithm.subst_logGammaData,
    Syn.subst_var,Syn.inst_zero,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    Prf.eqCongr1 (logGammaData (var 0) one : PTm (n+1)) eq

private theorem exact_stirling_normalization (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF (addF H SF) (factorialLogData N)
      (addData (hd N one) (sumData N one zero)) := by
  have h := source N hN
  have increment := GaussianStirlingGammaLogShift.log_gamma_increment N one h
  have eq := GaussianGammaCompactCutoffAlignment.cross_data_congr logGammaF (addF H logGammaF)
    _ _ _ _ (factorial_datum N).eqSymm (.eqRefl _) increment
  have hH := GaussianHarmonicLogarithmName.name_regular N one h
  have normal := GaussianNamedGammaHalfShift.add_cross H H logGammaF SF (hd N one) (hd N one)
    (logGammaData N one) (sumData N one zero) hH hH (log_gamma_regular _ _ h)
    (add_fast remainderF normalizationF (remainderData N one zero) (normalization N)
      (remainder_regular _ _ _ h) (normalization_regular _ _ _ h))
    (cross_refl _ _ hH) (cross_symm _ _ _ _ (logarithmic_cancellation N one zero h))
  exact cross_trans _ _ _ _ _ _ eq normal

private theorem remainder_sampler :
    GaussianStirlingGlobalBounds.remainderF = GaussianStirlingMultiplicativeAlgebra.remainderF := rfl

private theorem remainder_datum (a b x : PTm n) :
    GaussianStirlingGlobalBounds.remainderData a b x =
      GaussianStirlingMultiplicativeAlgebra.remainderData a b x := rfl

private theorem remainder_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate remainderF constantF (remainderData N one zero) (correction N) one (cube N) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.shift
  have basic := GaussianStirlingCubicRate.cubic_rate_at p q (sh N) one zero (source (sh N) hs)
  have eq : Δ ⊢[PRAAx] cube (one : PTm (n+2)) ≐ one := by unfold cube; ipra_ring
  have obs := distance_congr (.eqRefl _) (.eqRefl _)
    (congrAdd (congrMul (congrMul eq (.eqRefl _)) (.eqRefl _)) (.eqRefl _)) (.eqRefl _) basic
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNamedInverseRate.rateNumerator,correction,cube,Δ,sh,Syn.shift,p,q,one,
    GaussianStirlingMultiplicativeAlgebra.subst_remainderData,GaussianStirlingRationalTelescopers.subst_upperValue,
    remainder_sampler,remainder_datum,
    LeanProofs.IPRA.PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using obs

theorem factorial_logarithm_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate logGammaF approximationF (factorialLogData N) (approximationData N)
      one (cube N) := by
  let B := cube N
  let N₁ := leadingNumerator one B zero one
  let D₁ := leadingDenominator B one
  let N₂ := leadingNumerator zero one N₁ D₁
  let D₂ := leadingDenominator one D₁
  let x := normalization N
  let y := hd N one
  let y' := approximationData N
  let z := addData y (sumData N one zero)
  let F := addF H SF
  have hs := source N hN
  have hb := cube_positive N hN
  have hd₁ : Γ ⊢[PRAAx] le one D₁ := positive_product _ _ hb (le_refl one)
  have hd₂ : Γ ⊢[PRAAx] le one D₂ := positive_product _ _ (le_refl one) hd₁
  have normal := GaussianNamedAddRate.independent_rate remainderF normalizationF constantF normalizationF
    (remainderData N one zero) x (correction N) x one B zero one hb (le_refl one)
    (remainder_rate N hN) (self_rate normalizationF x (normalization_regular _ _ _ hs))
  have shifted := GaussianNamedAddRate.independent_rate H SF H (addF constantF normalizationF)
    y (sumData N one zero) y (addData (correction N) x) zero one N₁ D₁ (le_refl one) hd₁
    (self_rate H y (GaussianHarmonicLogarithmName.name_regular _ _ hs)) normal
  have small := GaussianNamedRateRadius.weaken F approximationF z y' N₂ D₂ one B hd₂ hb
    (le_of_eq_add (d := zero) (by unfold N₂ D₂ N₁ D₁ leadingNumerator leadingDenominator; ipra_ring)) shifted
  exact GaussianNamedRateTransport.transport F approximationF logGammaF approximationF z y' (factorialLogData N) y'
    one B hb small (exact_stirling_normalization N hN) (cross_refl _ _ (approximation_regular N hN))

theorem actual_original_factorial_logarithm_cubic_Stirling_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ independentRate logGammaF approximationF (factorialLogData (var 0)) (approximationData (var 0))
      one (cube (var 0))) :=
  closeUniv 1 (.impI (factorial_logarithm_rate _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerStirlingGamma
