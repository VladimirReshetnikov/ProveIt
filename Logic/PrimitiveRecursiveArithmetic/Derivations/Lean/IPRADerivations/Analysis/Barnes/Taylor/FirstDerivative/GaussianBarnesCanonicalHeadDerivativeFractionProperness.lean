import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadCorrectionExponentialDerivative
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadPolynomialDerivative
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFiniteProperness

/-!
# Equivalent fractions in the original finite Barnes derivative data

At the same finite cutoff, the original polynomial, its slope, the
exact total correction, and the correction slope all depend only on
the rational Gaussian argument. This identifies the data used by the
original correction exponential and its derivative under rescaling.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivativeFractionProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalFiniteProperness (scaled_fraction_equal)
open GaussianBarnesCanonicalHeadCorrectionDerivative (halfSquare slope total_formula)
open GaussianBarnesCanonicalHeadExponentialFactors (exponentData)
open GaussianBarnesCanonicalHeadPolynomial (polynomial degree original_evaluation)
open GaussianBarnesCanonicalHeadPolynomialDerivative (powerSlope)
open GaussianGammaEncodingRescaling (fraction_denominator_congr)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMonicReduction (evaluate_congr)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem total_equal (z w B D N : PTm n) (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx] total z B N ≐ total w D N := by
  have a := fraction_denominator_congr (Γ := Γ) z (two*B) (B*two) (mul_comm two B)
  have b := fraction_denominator_congr (Γ := Γ) w (D*two) (two*D) (mul_comm D two)
  have half := a.eqTrans ((scaled_fraction_equal z w B D two hb hd (le_succ_self one) eq).eqTrans b)
  have squares : Γ ⊢[PRAAx] halfSquare z B ≐ halfSquare w D := qmul_congr eq half
  exact (total_formula z B N hb).eqTrans ((qsub_congr (qmul_congr squares (.eqRefl _))
    (qmul_congr (.eqRefl _) eq)).eqTrans (total_formula w D N hd).eqSymm)

theorem correction_slope_equal (z w B D N : PTm n) (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] slope z B N ≐ slope w D N :=
  qsub_congr (qmul_congr eq (.eqRefl _)) (.eqRefl _)

theorem exponent_data_equal (z w B D N : PTm n) (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx] exponentData z B N ≐ exponentData w D N := by
  have e := total_equal z w B D N hb hd eq
  let C := GaussianGammaCanonicalExponent.constantF
  change Γ ⊢[PRAAx] GaussianGammaFiniteApproximantName.exponentialInputData C (total z B N) ≐
    GaussianGammaFiniteApproximantName.exponentialInputData C (total w D N)
  simpa only [GaussianGammaFiniteApproximantName.exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianNameBounds.subst_U,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (GaussianGammaFiniteApproximantName.exponentialInputData C (var 0) : PTm 1)
      (σ := ![total z B N]) (σ' := ![total w D N]) (fun i => by fin_cases i; exact e)

theorem original_power_equal (z w B D N : PTm n) (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx] powerProduct z B N ≐ powerProduct w D N :=
  (original_evaluation z B N hb).eqSymm.eqTrans
    ((evaluate_congr (.eqRefl _) eq).eqTrans (original_evaluation w D N hd))

theorem power_slope_equal (z w B D N : PTm n) (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] powerSlope z B N ≐ powerSlope w D N := by
  unfold powerSlope
  ipra_congr (GaussianRationalFirstOrderPolynomial.slope (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl (polynomial N), eq, .eqRefl (degree N)]

theorem actual_Barnes_finite_derivative_data_fraction_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let w := var 1
     let B := var 2
     let D := var 3
     let N := var 4
     (le one B ⋏ (le one D ⋏ (ofGaussian z B ≐ ofGaussian w D))) ⟶
       ((powerProduct z B N ≐ powerProduct w D N) ⋏ ((powerSlope z B N ≐ powerSlope w D N) ⋏
         ((exponentData z B N ≐ exponentData w D N) ⋏ (slope z B N ≐ slope w D N))))) :=
  closeUniv 5 (.impI (.andI
    (original_power_equal _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (.andI (power_slope_equal _ _ _ _ _ Prf.hyp0.andE₂.andE₂)
      (.andI (exponent_data_equal _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
        (correction_slope_equal _ _ _ _ _ Prf.hyp0.andE₂.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivativeFractionProperness
