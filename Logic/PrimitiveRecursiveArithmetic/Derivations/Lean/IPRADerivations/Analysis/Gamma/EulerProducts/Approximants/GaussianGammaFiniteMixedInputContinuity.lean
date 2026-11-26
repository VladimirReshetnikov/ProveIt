import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteInputContinuity
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Original finite Q_N continuity at independently encoded inputs

Only the native denominators are cleared. The actual original Q_N data
are invariant under that rescaling, including their internally computed
exponential radii and clocks. The uniform gain and both requested
observation errors are therefore unchanged.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteMixedInputContinuity

open_ipra
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianGammaFiniteInputContinuity (gain)
open GaussianGammaEncodingRescaling (fraction_rescale fraction_denominator_congr q_data_rescale)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open ComplexLogarithmRemainder (scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem q_data_denominator_congr (z B C N : PTm n) (h : Γ ⊢[PRAAx] B ≐ C) : Γ ⊢[PRAAx]
    qData z B N ≐ qData z C N := by
  ipra_congr (qData (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, h, .eqRefl N]

theorem original_mixed_independent_rate (z w R B C A D N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded w (R*C))
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) A D) : Γ ⊢[PRAAx]
    independentRate qF qF (qData z B N) (qData w C N) (gain R N*A) D := by
  let Z := scale C z
  let W := scale B w
  let H := C*B
  have hH := positive_product C B hC hB
  have hzH : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded Z (R*H) :=
    le_congr (.eqRefl _) (by dsimp only [H]; ipra_ring) (ComplexLogarithmRemainder.bounded_scale C hz)
  have hwH : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded W (R*H) :=
    le_congr (.eqRefl _) (by dsimp only [H]; ipra_ring) (ComplexLogarithmRemainder.bounded_scale B hw)
  have left : Γ ⊢[PRAAx] ofGaussian Z H ≐ ofGaussian z B := fraction_rescale z B C hB hC
  have right : Γ ⊢[PRAAx] ofGaussian W H ≐ ofGaussian w C :=
    (fraction_denominator_congr W H (B*C) (mul_comm C B)).eqTrans (fraction_rescale w C B hC hB)
  have close := distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) hd
  have scaled := GaussianGammaFiniteInputContinuity.original_independent_rate Z W R H A D N
    (.andI hN (.andI hH (.andI hD (.andI hzH (.andI hwH close)))))
  have leftData := q_data_rescale z B C N hB hC
  have rightData : Γ ⊢[PRAAx] qData W H N ≐ qData w C N :=
    (q_data_denominator_congr W H (B*C) N (mul_comm C B)).eqTrans (q_data_rescale w C B N hC hB)
  have leftCross := GaussianGammaInputProperness.code_data_cross qF _ _
    (q_regular z B N hN) (q_regular Z H N hN) leftData.eqSymm
  have rightCross := GaussianGammaInputProperness.code_data_cross qF _ _
    (q_regular w C N hN) (q_regular W H N hN) rightData.eqSymm
  exact GaussianNamedRateTransport.transport qF qF qF qF _ _ _ _ _ _ hD scaled leftCross rightCross

theorem original_mixed_observations (p q z w R B C A D N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded w (R*C))
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) A D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 qF p (qData z B N)) (ap2 qF q (qData w C N))
      (rateNumerator (gain R N*A) D p q) (rateDenominator D p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q
    (original_mixed_independent_rate z w R B C A D N hN hB hC hD hz hw hd)

def input (z w R B C A D N : PTm n) : Fm PTm n :=
  le one N ⋏ (le one B ⋏ (le one C ⋏ (le one D ⋏
    (ComplexLogarithmRemainder.bounded z (R*B) ⋏
      (ComplexLogarithmRemainder.bounded w (R*C) ⋏ distanceBounded (ofGaussian z B) (ofGaussian w C) A D)))))

theorem original_finite_Q_mixed_encoding_uniform_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate qF qF (qData (var 0) (var 3) (var 7)) (qData (var 1) (var 4) (var 7))
        (gain (var 2) (var 7)*var 5) (var 6)) :=
  closeUniv 8 (.impI (original_mixed_independent_rate _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteMixedInputContinuity
