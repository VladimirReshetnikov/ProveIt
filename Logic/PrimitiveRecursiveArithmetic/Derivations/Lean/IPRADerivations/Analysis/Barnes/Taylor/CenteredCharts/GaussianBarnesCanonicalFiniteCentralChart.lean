import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalPrefixChart
import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalFiniteLogFractionProperness

/-!
# Chart independence of the original finite Barnes scalar

The central exponential uses a prefix with identical data in each
chart and a finite tail with equivalent observations. Both facts apply
at the original cutoff, so the product is independent of presentation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralChart

open_ipra
open GaussianBarnesCanonicalFiniteCentralExponential (prefixExpData prefix_exp_regular finiteNameF finiteData)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (prefixF)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaInputProperness (code_data_cross)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF prefixF
local notation "T" => GaussianBarnesCanonicalTailExponential.finiteF
local notation "td" => GaussianBarnesCanonicalTailExponential.finiteData
local notation "L" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "ld" => GaussianBarnesCanonicalFiniteLog.data

/-- The actual scalar at the same finite cutoff in two rational charts. -/
theorem proper (z w R B D r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent finiteNameF finiteNameF (finiteData z R B r) (finiteData w R D r) := by
  let N := initial R
  have hzN := initial_source z R B hz
  have hwN := initial_source w R D hw
  have hzE := prefix_exp_regular (Γ := Γ) z R B
  have hwE := prefix_exp_regular (Γ := Γ) w R D
  have prefix_eq := code_data_cross E (prefixExpData z R B) (prefixExpData w R D) hzE hwE
    (GaussianBarnesCanonicalPrefixChart.prefix_exponential_data_proper z w R B D hz.andE₁ hw.andE₁ he)
  have tail := GaussianRadiusExponentialName.cross_proper L L (GaussianBarnesCanonicalFiniteLog.radius R)
    (ld z R B N r) (ld w R D N r) (GaussianBarnesCanonicalFiniteLog.exponential_input z R B N r hzN)
    (GaussianBarnesCanonicalFiniteLog.exponential_input w R D N r hwN)
    (GaussianBarnesCanonicalFiniteLogFractionProperness.proper z w R R B D N r hzN hwN he)
  exact multiply_cross E E T T (prefixExpData z R B) (prefixExpData w R D) (td z R B N r) (td w R D N r)
    hzE hwE (GaussianBarnesCanonicalTailExponential.finite_regular z R B N r hzN)
    (GaussianBarnesCanonicalTailExponential.finite_regular w R D N r hwN) prefix_eq tail

theorem actual_Barnes_finite_central_scalar_chart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let r := var 5
     (source z R B ⋏ source w R D) ⟶ ofGaussian z B ≐ ofGaussian w D ⟶
       crossEquivalent finiteNameF finiteNameF (finiteData z R B r) (finiteData w R D r)) :=
  closeUniv 6 (.impI (.impI (proper _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralChart
