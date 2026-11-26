import IPRADerivations.Analysis.GaussianBarnesCanonicalHigherCofinal
import IPRADerivations.Analysis.GaussianNamedLipschitzRate

/-!
# Rate from the literal higher coefficient prefixes to their cofinal names

At every encoded order and every pair of observation precisions,
the rate from the retained finite coefficient sum is controlled by
the inverse-square tail starting at the end of that prefix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherCofinalRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherCofinal (data nameF sample_at prefix_error regular)
open GaussianBarnesCanonicalHigherRows (coefficientGain)
open GaussianBarnesCanonicalHigherTail (value)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem finite_rate (z R B j r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate constantF nameF (value z B (initial R) j r) (data z R B j)
      (coefficientGain j) (initial R+r) := by
  let N := initial R
  let K := N+r
  let v := value z B N j r
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  apply GaussianNamedLipschitzRate.independent_rate constantF nameF v (data z R B j) (coefficientGain j) K one
    hK (constant_regular _) (regular z R B j h)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let K' := initial (sh R)+sh r
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have hk : Δ ⊢[PRAAx] le one K' := le_trans (initial_positive (sh R)) (le_add_right _ _)
  have e := distance_symmetric _ _ _ _ (positive_product _ _ hk (unit_positive p))
    (prefix_error p (sh z) (sh R) (sh B) (sh j) (sh r) hs)
  simpa only [diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,sh,Δ,p,K,K',N,v,data,GaussianBarnesCanonicalHigherTail.subst_data,
    GaussianBarnesCanonicalHigherTail.subst_value,
    GaussianBarnesCanonicalLogSchedule.subst_initial,GaussianBarnesCanonicalHigherRows.subst_coefficientGain,
    PTm.subst_add,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distance_congr (constant_at p _).eqSymm (sample_at p (sh z) (sh R) (sh B) (sh j)).eqSymm
      (congrAdd (.eqRefl _) (one_mul K').eqSymm) (.eqRefl _) e

theorem actual_Barnes_all_higher_coefficients_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let j := var 3
     let r := var 4
     source z R B ⟶ independentRate constantF nameF (value z B (initial R) j r) (data z R B j)
       (coefficientGain j) (initial R+r)) :=
  closeUniv 5 (.impI (finite_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherCofinalRate
