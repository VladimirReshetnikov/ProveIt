/-
Exact quadratic specialization of the original Mercator program, at a
possibly sharper radius than its native input certificate.
-/
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmTaylorRemainder
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmQuadraticRate

open_ipra
open ComplexLogarithmRemainder (code)
open GaussianFiniteLogarithmPolynomial (coefficient sourceTerm value source_term_at)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLocalLogarithmName (source pointF data)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (qadd qmul ofGaussian canonical qmul_canonical)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (power qone)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quadratic (w : PTm n) : PTm n := qadd w (qmul (coefficient one) (qmul w w))
def errorNumerator (A : PTm n) : PTm n := GaussianFiniteLogarithmTaylorRemainder.numerator A two
def errorDenominator (A B : PTm n) : PTm n := GaussianFiniteLogarithmTaylorRemainder.denominator A B two

@[simp] theorem subst_quadratic {m : ℕ} (σ : Fin n → PTm m) (w : PTm n) :
    Syn.subst σ (quadratic w) = quadratic (Syn.subst σ w) := by simp [quadratic]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (errorNumerator A) = errorNumerator (Syn.subst σ A) := by simp [errorNumerator]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (errorDenominator A B) = errorDenominator (Syn.subst σ A) (Syn.subst σ B) := by simp [errorDenominator]

private theorem coeff_zero : Γ ⊢[PRAAx] coefficient (zero : PTm n) ≐ qone := by
  change Γ ⊢[PRAAx] ofGaussian (code ⟨LogarithmExponentialCoefficients.evenBit zero,
    LogarithmExponentialCoefficients.oddBit zero⟩ (ZT.ofNat zero)) one ≐
      ofGaussian (code ⟨one,zero⟩ (ZT.ofNat zero)) one
  ipra_congr (ofGaussian (code ⟨var 0,var 1⟩ (ZT.ofNat zero)) one : PTm 2) with
    [LogarithmExponentialCoefficients.evenBit_zero, LogarithmExponentialCoefficients.oddBit_zero] using [ZT.subst, ZT.ofNat]

theorem exact_value (w : PTm n) (hw : Γ ⊢[PRAAx] canonical w) :
    Γ ⊢[PRAAx] value two w ≐ quadratic w := by
  have firstLeaf : Γ ⊢[PRAAx] qmul (coefficient zero) (power w one) ≐ w :=
    (qmul_congr coeff_zero (GaussianRationalPowerAlgebra.power_one w hw)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone w).eqTrans
        (GaussianReciprocalHorner.qmul_one_right w hw))
  have first := GaussianRationalFiniteSum.sum_singleton sourceTerm w
    (by rw [source_term_at]; exact firstLeaf) hw
  have second : Γ ⊢[PRAAx] inst2 sourceTerm one w ≐ qmul (coefficient one) (qmul w w) := by
    rw [source_term_at]
    exact qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.power_two w hw)
  exact (GaussianRationalFiniteSum.sum_succ sourceTerm one w).eqTrans (qadd_congr first second)

theorem rate_at_radius (z R D A B : PTm n) (hs : Γ ⊢[PRAAx] source z R D)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] lt A B)
    (hw : Γ ⊢[PRAAx] bounded (ofGaussian z D) A B) :
    Γ ⊢[PRAAx] independentRate pointF constantF (data z R D) (quadratic (ofGaussian z D))
      (errorNumerator A) (errorDenominator A B) := by
  let x := data z R D
  let w := ofGaussian z D
  let y := value two w
  let u := quadratic w
  let E := errorDenominator A B
  have hE : Γ ⊢[PRAAx] le one E := GaussianFiniteLogarithmTaylorRemainder.denominator_positive A B two hB hAB
  have h := GaussianLocalLogarithmTaylorRemainder.rate_at_radius two z R D A B hs hB hAB hw
  have eq := exact_value w (GaussianRationalHorner.ofGaussian_canonical z D hs.andE₁)
  exact GaussianNamedRateTransport.transport pointF constantF pointF constantF x y x u (errorNumerator A) E hE h
    (cross_refl _ _ (GaussianLocalLogarithmName.name_regular z R D hs))
    (GaussianGammaWeierstrassApproximant.constant_data_cross u y eq.eqSymm)

theorem actual_Mercator_second_order_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 2) ⋏ (le one (var 4) ⋏ (lt (var 3) (var 4) ⋏
      bounded (ofGaussian (var 0) (var 2)) (var 3) (var 4)))) ⟶
      independentRate pointF constantF (data (var 0) (var 1) (var 2)) (quadratic (ofGaussian (var 0) (var 2)))
        (errorNumerator (var 3)) (errorDenominator (var 3) (var 4))) :=
  closeUniv 5 (.impI (rate_at_radius _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmQuadraticRate
