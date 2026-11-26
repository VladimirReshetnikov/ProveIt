import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNative
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalEndpoints

/-!
# The normalized derivative target of the original negative Gamma

The target is the original negative Gamma times the shifted digamma.
Its two identities use the original reciprocal pair and the original
positive first Euler integral. They specify the target before
estimating the negative Gamma difference quotients.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDerivativeTarget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalCorrection (correction guard)
open GaussianGammaNegativeCriticalEndpoints (nameData shifted_source)
open GaussianGammaNegativeIntervalNative (argument negative_source negative_regular product productData original_product)
open GaussianGammaReciprocalInverse (gammaF gamma_product)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative distributive multiply_one_left oneF one_fast)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "P" => GaussianGammaC7Name.nameF
local notation "E" => GaussianEulerLogarithmicImproperName.nameF
local notation "G" => GaussianGammaNegativeIntervalNative.data
local notation "Gplus" => GaussianStirlingGammaLogarithm.gammaData
local notation "Dplus" => GaussianGammaDigammaNative.derivativeData

def nameF : PR 2 := multiplyF gammaF S
def data (a b N : PTm n) : PTm n := multiplyData gammaF S (G a b N) (nameData a b N)
def reciprocalData (a b N : PTm n) : PTm n := GaussianGammaC7Name.data (argument a b N) (succ (succ N)) b
def shiftedCorrectionData (a b N : PTm n) : PTm n :=
  multiplyData gammaF constantF (Gplus (b+a) b) (correction a b N)

theorem target_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN nameF (data a b N) :=
  multiply_fast _ _ _ _ (negative_regular a b N h) (GaussianGammaNegativeCriticalEndpoints.name_regular a b N h)

theorem reciprocal_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN P (reciprocalData a b N) :=
  GaussianGammaC7Name.name_regular _ _ _ (negative_source a b N h).andE₁

theorem normalized_target (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF P nameF) S (multiplyData P nameF (reciprocalData a b N) (data a b N))
      (nameData a b N) := by
  let x := reciprocalData a b N
  let y := G a b N
  let z := nameData a b N
  have hx := reciprocal_regular a b N h
  have hy := negative_regular a b N h
  have hz := GaussianGammaNegativeCriticalEndpoints.name_regular a b N h
  have inv := gamma_product _ _ _ _ _ (negative_source a b N h)
  have e := cross_trans _ _ _ _ _ _ inv (GaussianBoundedInverseApartness.ones_equivalent x z)
  have trim := multiply_cross (multiplyF P gammaF) oneF S S (multiplyData P gammaF x y) z z z
    (multiply_fast _ _ _ _ hx hy) (one_fast _) hz hz e (cross_refl _ _ hz)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative P gammaF S x y z hx hy hz))
    (cross_trans _ _ _ _ _ _ trim (multiply_one_left _ _ hz))

theorem scaled_target (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF constantF nameF) (addF E (multiplyF gammaF constantF))
      (multiplyData constantF nameF (product a b N) (data a b N))
      (addData (Dplus (b+a) b) (shiftedCorrectionData a b N)) := by
  let c := product a b N
  let g := G a b N
  let s := nameData a b N
  let w := Gplus (b+a) b
  let u := GaussianGammaDigammaNative.data (b+a) b
  let v := correction a b N
  let F := GaussianGammaDigammaNative.nameF
  have hc := constant_regular (Γ := Γ) c
  have hg := negative_regular a b N h
  have hs := GaussianGammaNegativeCriticalEndpoints.name_regular a b N h
  have source := shifted_source a b h
  have hw := GaussianStirlingGammaLogarithm.gamma_regular _ _ source
  have hu := GaussianGammaDigammaNative.name_regular _ _ source
  have hv := constant_regular (Γ := Γ) v
  have move := multiply_cross (multiplyF constantF gammaF) gammaF S S (productData a b N) w s s
    (multiply_fast _ _ _ _ hc hg) hw hs hs (original_product a b N h) (cross_refl _ _ hs)
  have identify := GaussianNamedGammaHalfShift.add_cross (multiplyF gammaF F) E
    (multiplyF gammaF constantF) (multiplyF gammaF constantF) (multiplyData gammaF F w u) (Dplus (b+a) b)
    (shiftedCorrectionData a b N) (shiftedCorrectionData a b N)
    (multiply_fast _ _ _ _ hw hu) (GaussianGammaDigammaNative.derivative_regular _ _ source)
    (multiply_fast _ _ _ _ hw hv) (multiply_fast _ _ _ _ hw hv)
    (GaussianGammaDigammaNative.gamma_times_digamma _ _ source) (cross_refl _ _ (multiply_fast _ _ _ _ hw hv))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative constantF gammaF S c g s hc hg hs))
    (cross_trans _ _ _ _ _ _ move (cross_trans _ _ _ _ _ _ (distributive gammaF F constantF w u v hw hu hv) identify))

theorem actual_original_negative_Gamma_derivative_target_normalized_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶
        crossEquivalent (multiplyF P nameF) S
          (multiplyData P nameF (reciprocalData (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2)))
          (nameData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (normalized_target _ _ _ Prf.hyp0))

theorem actual_original_negative_Gamma_derivative_target_scaled_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶
        crossEquivalent (multiplyF constantF nameF) (addF E (multiplyF gammaF constantF))
          (multiplyData constantF nameF (product (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2)))
          (addData (Dplus (var 1+var 0) (var 1)) (shiftedCorrectionData (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (scaled_target _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDerivativeTarget
