import IPRADerivations.Analysis.Gamma.EulerProducts.RationalLogarithm.GaussianGammaEulerRationalLogConvergenceSource
import IPRADerivations.Analysis.Logarithm.PositiveAxis.NamedValues.GaussianNamedPositiveLogarithmRate

/-!
# Actual finite Euler logarithms converge to the original log Gamma

On the common certified positive margin, the original named logarithm
multiplies the Euler inverse error by the fixed constant 72. The
endpoint names are the literal finite inverse logarithm and log Gamma.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogConvergence

open_ipra
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator)
open GaussianGammaEulerRationalLogConvergenceSource (finiteInputF nativeInputF finiteInputData nativeInputData
  finiteLogData nativeLogData logMargin finiteRadius nativeRadius finite_log_input native_log_input
  input_rate finite_log_cross native_log_cross)
open GaussianGammaEulerRationalLogMargin (source denominator_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianGammaEulerRationalLog.nameF
local notation "fd" => GaussianGammaEulerRationalLog.data
local notation "L" => GaussianNamedPositiveLogarithm.nameF

def rateCoefficient (a b : PTm n) : PTm n := logMargin*coefficientNumerator a b

ipra_subst rateCoefficient [logMargin, GaussianGammaEulerRationalLogMargin.margin, two]

set_option maxHeartbeats 700000 in
theorem actual_rate (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] independentRate F logGammaF (fd N a b) (logGammaData a b)
      (rateCoefficient a b) (coefficientDenominator a one N) := by
  have pos := denominator_positive N a b h
  have rate := GaussianNamedPositiveLogarithmRate.log_rate finiteInputF nativeInputF
    (finiteInputData N a b) (nativeInputData a b) logMargin (finiteRadius N a b) (nativeRadius a b)
    (coefficientNumerator a b) (coefficientDenominator a one N)
    (finite_log_input N a b h) (native_log_input a b h.andE₁) pos (input_rate N a b h)
  exact GaussianNamedRateTransport.transport (L finiteInputF) (L nativeInputF) F logGammaF
    (finiteLogData N a b) (nativeLogData a b) (fd N a b) (logGammaData a b) _ _ pos rate
    (finite_log_cross N a b h) (native_log_cross a b h.andE₁)

theorem actual_original_Euler_log_convergence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ independentRate F logGammaF (fd (var 0) (var 1) (var 2))
      (logGammaData (var 1) (var 2)) (rateCoefficient (var 1) (var 2)) (coefficientDenominator (var 1) one (var 0))) :=
  closeUniv 3 (.impI (actual_rate _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogConvergence
