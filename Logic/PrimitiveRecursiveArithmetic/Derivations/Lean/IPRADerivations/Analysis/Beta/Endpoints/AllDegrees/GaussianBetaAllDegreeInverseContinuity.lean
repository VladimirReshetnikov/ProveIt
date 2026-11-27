import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaUniformEndpointBound
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.Continuity.GaussianGammaFiniteInputContinuity

/-!
# Input continuity of the actual all-degree finite Euler reciprocal

The actual beta endpoint inverse has one numerical all-sample bound
independent of observation precision. Its squared bound multiplies the
original Q_N input rate. Actual named inverse products and independent
clock transport yield the same rate for the unchanged reciprocal program
with its all-degree certified data. Every finite N>=1 is allowed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeInverseContinuity

open_ipra
open GaussianBetaAllDegreeEulerInverse (endpointF endpointData nameF data)
open GaussianBetaUniformEndpointBound (endpointBound)
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product ofGaussian)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z w R B C A N : PTm n) : Fm PTm n :=
  GaussianBetaAllDegreeEulerInverse.source z R B A N ⋏ GaussianBetaAllDegreeEulerInverse.source w R C A N
def gain (R A N : PTm n) : PTm n := endpointBound R A N*endpointBound R A N*GaussianGammaFiniteInputContinuity.gain R N
def input (z w R B A X Y N : PTm n) : Fm PTm n := source z w R B B A N ⋏
  (le one Y ⋏ distanceBounded (ofGaussian z B) (ofGaussian w B) X Y)
ipra_subst source
ipra_subst gain
ipra_subst input

theorem rate_congr (F G : PR 2) (x y X X' Y Y' : PTm n)
    (hX : Γ ⊢[PRAAx] X ≐ X') (hY : Γ ⊢[PRAAx] Y ≐ Y')
    (h : Γ ⊢[PRAAx] independentRate F G x y X Y) : Γ ⊢[PRAAx] independentRate F G x y X' Y' := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (Syn.shift (Syn.shift x))
      (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift X)) (Syn.shift (Syn.shift Y)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have xs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift X) ≐ Syn.shift (Syn.shift X') := hX.shift.shift
  have ys : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift Y) ≐ Syn.shift (Syn.shift Y') := hY.shift.shift
  refine .allI (.allI ?_)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (congrAdd (congrMul (congrMul xs (.eqRefl _)) (.eqRefl _)) (congrMul ys (.eqRefl _)))
    (congrMul (congrMul ys (.eqRefl _)) (.eqRefl _)) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs)

theorem endpoint_inverse_input (z w R B C A N X Y : PTm n)
    (h : Γ ⊢[PRAAx] source z w R B C A N) (hY : Γ ⊢[PRAAx] le one Y)
    (hQ : Γ ⊢[PRAAx] independentRate qF qF (qData z B N) (qData w C N) X Y) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.input qF qF endpointF endpointF (qData z B N) (qData w C N)
      (endpointData z B N) (endpointData w C N) (endpointBound R A N) one X Y := by
  exact .andI (le_refl one) (.andI hY (.andI
    (.andI (q_regular z B N h.andE₁.andE₂) (q_regular w C N h.andE₂.andE₂))
    (.andI (.andI (GaussianBetaAllDegreeEulerInverse.endpoint_regular z R B A N h.andE₁)
      (GaussianBetaAllDegreeEulerInverse.endpoint_regular w R C A N h.andE₂))
    (.andI (.andI (GaussianBetaUniformEndpointBound.original_endpoint_disk z R B A N h.andE₁)
      (GaussianBetaUniformEndpointBound.original_endpoint_disk w R C A N h.andE₂))
    (.andI (.andI
      (GaussianBetaUpperEndpointInverse.original_upper_product z R B A one N h.andE₁.andE₁ (le_refl one) h.andE₁.andE₂)
      (GaussianBetaUpperEndpointInverse.original_upper_product w R C A one N h.andE₂.andE₁ (le_refl one) h.andE₂.andE₂)) hQ)))))

theorem original_from_Q_rate (z w R B C A N X Y : PTm n)
    (h : Γ ⊢[PRAAx] source z w R B C A N) (hY : Γ ⊢[PRAAx] le one Y)
    (hQ : Γ ⊢[PRAAx] independentRate qF qF (qData z B N) (qData w C N) X Y) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z B N) (data w C N) (endpointBound R A N*endpointBound R A N*X) Y := by
  have candidate := GaussianNamedInverseRate.inverse_rate qF qF endpointF endpointF (qData z B N) (qData w C N)
    (endpointData z B N) (endpointData w C N) (endpointBound R A N) one X Y (endpoint_inverse_input z w R B C A N X Y h hY hQ)
  have normalized := rate_congr endpointF endpointF (endpointData z B N) (endpointData w C N)
    _ _ _ Y (.eqRefl _) (by ipra_ring) candidate
  exact GaussianNamedRateTransport.transport endpointF endpointF nameF nameF (endpointData z B N) (endpointData w C N)
    (data z B N) (data w C N) _ Y hY normalized
    (GaussianBetaAllDegreeEulerInverse.original_inverse z R B A N h.andE₁).andE₂
    (GaussianBetaAllDegreeEulerInverse.original_inverse w R C A N h.andE₂).andE₂

theorem original_independent_rate (z w R B A X Y N : PTm n) (h : Γ ⊢[PRAAx] input z w R B A X Y N) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z B N) (data w B N) (gain R A N*X) Y := by
  have hs : Γ ⊢[PRAAx] GaussianGammaFiniteInputContinuity.input z w R B X Y N :=
    .andI h.andE₁.andE₁.andE₂ (.andI h.andE₁.andE₁.andE₁.andE₂.andE₁.andE₁
      (.andI h.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁.andE₂.andE₁.andE₂
        (.andI h.andE₁.andE₂.andE₁.andE₂.andE₁.andE₂ h.andE₂.andE₂))))
  exact rate_congr nameF nameF _ _ _ _ _ _ (by unfold gain; ipra_ring) (.eqRefl _)
    (original_from_Q_rate z w R B B A N _ Y h.andE₁ h.andE₂.andE₁
      (GaussianGammaFiniteInputContinuity.original_independent_rate z w R B X Y N hs))

theorem original_observations (p q z w R B A X Y N : PTm n) (h : Γ ⊢[PRAAx] input z w R B A X Y N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z B N)) (ap2 nameF q (data w B N))
      (rateNumerator (gain R A N*X) Y p q) (rateDenominator Y p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_independent_rate z w R B A X Y N h)

theorem original_all_degree_Euler_inverse_input_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate nameF nameF (data (var 0) (var 3) (var 7)) (data (var 1) (var 3) (var 7))
        (gain (var 2) (var 4) (var 7)*var 5) (var 6)) :=
  closeUniv 8 (.impI (original_independent_rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeInverseContinuity
