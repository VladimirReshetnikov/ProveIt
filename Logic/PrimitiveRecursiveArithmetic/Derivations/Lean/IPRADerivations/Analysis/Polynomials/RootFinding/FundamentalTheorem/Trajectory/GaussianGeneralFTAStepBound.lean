import IPRADerivations.Analysis.Polynomials.Evaluation.NamedValues.GaussianGeneralPolynomialSamples
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.Trajectory.GaussianGeneralFTARates

/-!
# The computed shrinking step for general coefficient names

The original coefficient-name and h+2 apartness assumptions supply the
actual sampled polynomial. All rate, nonconstancy, coefficient-lower and
step-constant obligations are discharged from the source's computed
constants. The point disk and its current actual residual budget are the
local hypotheses, to be supplied by the trajectory invariant. The result
is the unchanged displacement bounded by U C rho^j, with no monicity or
known leading degree assumption. Every numerical parameter is internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAStepBound

open_ipra
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants
  (B C QNum QDen rhoNum K)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sample sourceInput)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (lambdaDenominator referencePrecision)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem step_constant (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    B a x*GaussianNonmonicTravelCoefficientBound.weight N*lambdaDenominator h ≐ C a N h x := by
  have den : Γ ⊢[PRAAx] lambdaDenominator h ≐ pw two (h+one) :=
    congrAp2 powF (succ_eq_add_one h) (.eqRefl two)
  exact (congrMul (.eqRefl _) den).eqTrans (GaussianGeneralFTAConstants.C_factorization a N h x).eqSymm

theorem computed_rate_input (a : PR 3) (N h x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianNonmonicStepBound.rateInput N one (lambdaDenominator h) (B a x) one
      (QNum N) (QDen N) (rhoNum N) (K N) :=
  .andI (le_refl one) (.andI (GaussianGeneralFTAConstants.QDen_positive N)
    (.andI (GaussianGeneralFTAConstants.K_positive N hN)
      (.andI (le_of_lt (GaussianGeneralFTARates.rhoNum_below N hN))
        (.andI (GaussianGeneralFTARates.Q_le_rho_power N hN)
          (le_congr (one_mul one).eqSymm (step_constant a N h x).eqSymm
            (GaussianGeneralFTAConstants.C_positive a N h x hN))))))

theorem sampled_step_input (a : PR 3) (N k h s x z U V j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hs : Γ ⊢[PRAAx] le (referencePrecision h) s)
    (hV : Γ ⊢[PRAAx] le one V) (hVU : Γ ⊢[PRAAx] le V U)
    (hz : Γ ⊢[PRAAx] bounded z U V)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate (sample a N s x) z)
      (B a x*pw (QNum N) j) (pw (QDen N) j)) : Γ ⊢[PRAAx]
    GaussianNonmonicStepBound.input (sample a N s x) N z U V k one (lambdaDenominator h)
      (B a x) one (QNum N) (QDen N) (rhoNum N) (K N) j := by
  have hN := le_trans (Prf.andE₁ (Prf.andE₂ hSource)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hSource)))
  exact .andI (GaussianGeneralPolynomialSamples.tail_coefficient_input a N k h s x z U V hSource hs hV hVU hz)
    (.andI (computed_rate_input a N h x hN)
      (GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (one_mul _).eqSymm hResidual))

theorem numerator_value (a : PR 3) (N U h x j : PTm n) : Γ ⊢[PRAAx]
    GaussianNonmonicStepBound.numerator N U (lambdaDenominator h) (B a x) (rhoNum N) j ≐
      U*C a N h x*pw (rhoNum N) j :=
  congrMul (congrMul (.eqRefl U) (step_constant a N h x)) (.eqRefl _)

theorem denominator_value (N V j : PTm n) : Γ ⊢[PRAAx]
    GaussianNonmonicStepBound.denominator V one one (K N) j ≐ V*pw (K N) j := by
  unfold GaussianNonmonicStepBound.denominator
  ipra_ring

theorem displacement_bound (a : PR 3) (N k h s x z U V j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hs : Γ ⊢[PRAAx] le (referencePrecision h) s)
    (hV : Γ ⊢[PRAAx] le one V) (hVU : Γ ⊢[PRAAx] le V U)
    (hz : Γ ⊢[PRAAx] bounded z U V)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate (sample a N s x) z)
      (B a x*pw (QNum N) j) (pw (QDen N) j)) : Γ ⊢[PRAAx]
    bounded (GaussianNonmonicRD.delta N (sample a N s x) z)
      (U*C a N h x*pw (rhoNum N) j) (V*pw (K N) j) :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (numerator_value a N U h x j) (denominator_value N V j)
    (GaussianNonmonicStepBound.delta_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (sampled_step_input a N k h s x z U V j hSource hs hV hVU hz hResidual))

theorem displacement_program_bound (a : PR 3) (N k h s x z U V j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hs : Γ ⊢[PRAAx] le (referencePrecision h) s)
    (hV : Γ ⊢[PRAAx] le one V) (hVU : Γ ⊢[PRAAx] le V U)
    (hz : Γ ⊢[PRAAx] bounded z U V)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate (sample a N s x) z)
      (B a x*pw (QNum N) j) (pw (QDen N) j)) : Γ ⊢[PRAAx]
    bounded (ap3 GaussianNonmonicDisplacementRadius.deltaF N (sample a N s x) z)
      (U*C a N h x*pw (rhoNum N) j) (V*pw (K N) j) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianNonmonicDisplacementRadius.delta_program_at N (sample a N s x) z).eqSymm (.eqRefl _) (.eqRefl _)
    (displacement_bound a N k h s x z U V j hSource hs hV hVU hz hResidual)

theorem computed_rate_input_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ GaussianNonmonicStepBound.rateInput (var 0) one (lambdaDenominator (var 1)) (B a (var 2)) one
      (QNum (var 0)) (QDen (var 0)) (rhoNum (var 0)) (K (var 0))) :=
  closeUniv 3 (.impI (computed_rate_input _ _ _ _ Prf.hyp0))
theorem sampled_source_displacement_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (sourceInput a (var 0) (var 1) (var 2) (var 4) ⟶ le (referencePrecision (var 2)) (var 3) ⟶
      le one (var 7) ⟶ le (var 7) (var 6) ⟶ bounded (var 5) (var 6) (var 7) ⟶
      bounded (evaluate (sample a (var 0) (var 3) (var 4)) (var 5))
        (B a (var 4)*pw (QNum (var 0)) (var 8)) (pw (QDen (var 0)) (var 8)) ⟶
      bounded (GaussianNonmonicRD.delta (var 0) (sample a (var 0) (var 3) (var 4)) (var 5))
        (var 6*C a (var 0) (var 2) (var 4)*pw (rhoNum (var 0)) (var 8)) (var 7*pw (K (var 0)) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI (displacement_bound _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem sampled_source_program_displacement_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (sourceInput a (var 0) (var 1) (var 2) (var 4) ⟶ le (referencePrecision (var 2)) (var 3) ⟶
      le one (var 7) ⟶ le (var 7) (var 6) ⟶ bounded (var 5) (var 6) (var 7) ⟶
      bounded (evaluate (sample a (var 0) (var 3) (var 4)) (var 5))
        (B a (var 4)*pw (QNum (var 0)) (var 8)) (pw (QDen (var 0)) (var 8)) ⟶
      bounded (ap3 GaussianNonmonicDisplacementRadius.deltaF (var 0) (sample a (var 0) (var 3) (var 4)) (var 5))
        (var 6*C a (var 0) (var 2) (var 4)*pw (rhoNum (var 0)) (var 8)) (var 7*pw (K (var 0)) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI (displacement_program_bound _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAStepBound
