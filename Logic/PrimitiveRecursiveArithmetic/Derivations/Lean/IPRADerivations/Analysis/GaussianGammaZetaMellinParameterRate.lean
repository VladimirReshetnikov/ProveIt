import IPRADerivations.Analysis.GaussianGammaZetaMellinIdentity
import IPRADerivations.Analysis.GaussianGammaZetaDirichletProductParameterRate
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# An effective parameter rate for the original improper Mellin sampler

The checked rational identity holds for the actual improper sampler at
independent output clocks. It therefore transfers the product's exact
parameter rate to those same original samplers, including different
rational denominators for the two arguments.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinParameterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaZetaDirichletProductParameterRate (demand)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "I" => GaussianGammaZetaMellinImproper.nameF
local notation "datum" => GaussianGammaZetaMellinImproper.data

theorem original_demand_rate (s z w R B D j : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B (succ j)) (hw : Γ ⊢[PRAAx] S w R D (succ j))
    (close : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (demand s R (succ j)))) :
    Γ ⊢[PRAAx] independentRate I I (datum z R B j) (datum w R D j) one (unit s) :=
  GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive s)
    (GaussianGammaZetaDirichletProductParameterRate.original_demand_rate s z w R B D (succ j) hz hw close)
    (GaussianGammaZetaMellinIdentity.equivalent z R B j hz)
    (GaussianGammaZetaMellinIdentity.equivalent w R D j hw)

theorem actual_original_Mellin_parameter_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let s := var 0
       let z := var 1
       let w := var 2
       let R := var 3
       let B := var 4
       let D := var 5
       let j := var 6
       S z R B (succ j) ⟶ S w R D (succ j) ⟶
         distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (demand s R (succ j))) ⟶
         independentRate I I (datum z R B j) (datum w R D j) one (unit s)) :=
  closeUniv 7 (.impI (.impI (.impI (original_demand_rate _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinParameterRate
