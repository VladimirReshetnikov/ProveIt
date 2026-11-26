import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeCofinal
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Rate from the literal derivative prefixes to their cofinal name

The constant name of each exact derivative prefix compares to the
original cofinal sampler at every pair of observation precisions.
The leading error is exactly the reciprocal-square tail budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeCofinalRate

open_ipra
open GaussianBarnesCanonicalDerivativeCofinal (nameF sample_at prefix_error regular)
open GaussianBarnesCanonicalDerivativeRow (boundNumerator)
open GaussianBarnesCanonicalDerivativeTail (value)
open GaussianBarnesCanonicalLogCofinal (source data subst_data)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem finite_rate (z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate constantF nameF (value z B (initial R) r) (data z R B)
      (boundNumerator R) (initial R+r) := by
  let N := initial R
  let K := N+r
  let v := value z B N r
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  apply GaussianNamedLipschitzRate.independent_rate constantF nameF v (data z R B) (boundNumerator R) K one
    hK (constant_regular _) (regular z R B h)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let K' := initial (sh R)+sh r
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have hk : Δ ⊢[PRAAx] le one K' := le_trans (initial_positive (sh R)) (le_add_right _ _)
  have e := distance_symmetric _ _ _ _ (positive_product _ _ hk (unit_positive p))
    (prefix_error p (sh z) (sh R) (sh B) (sh r) hs)
  simpa only [diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,sh,Δ,p,K,K',N,v,subst_data,
    GaussianBarnesCanonicalDerivativeTail.subst_value,
    GaussianBarnesCanonicalLogSchedule.subst_initial,GaussianBarnesCanonicalDerivativeRow.subst_boundNumerator,
    PTm.subst_add,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distance_congr (constant_at p _).eqSymm (sample_at p (sh z) (sh R) (sh B)).eqSymm
      (congrAdd (.eqRefl _) (one_mul K').eqSymm) (.eqRefl _) e

theorem actual_Barnes_rational_derivative_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ independentRate constantF nameF (value z B (initial R) r) (data z R B)
       (boundNumerator R) (initial R+r)) :=
  closeUniv 4 (.impI (finite_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeCofinalRate
