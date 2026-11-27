import IPRADerivations.Analysis.Polynomials.Determinants.ErrorBounds.GaussianPolynomialDeterminantStageError
import IPRADerivations.Analysis.Polynomials.Products.Powers.GaussianRationalPolynomialPowers

/-!
# Exact coefficient-norm variation of the original actual powers

The original powerPrefix is literally the existing determinant word
stage on its repeated-input table. Actual factor lookup discharges all
original shape, factor-norm and factor-error contracts. The independently
proved stage-error induction therefore gives the exact finite bound
j A^(j-1) E, including zero error at the empty power and A=0.
Input buffers may contain arbitrary raw codes; all degrees, caps and
stages remain numerical internal parameters.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialPowerNormVariation

open_ipra
open GaussianRationalPolynomialPowers (table powerPrefix)
open GaussianCoefficientL1 (coefficientNorm subCoefficients)
open GaussianCoefficientNormOrder (coefficientNorm_congr subCoefficients_congr)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalPowerDifference (budget)
open GaussianPolynomialDeterminantStageNorm (factorBounds)
open GaussianPolynomialDeterminantStageError (factorDifferences)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem repeated_factor_bounds (C K A : PTm n) (h : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode A)) : Γ ⊢[PRAAx]
    factorBounds (table C K) K zero A := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (coefficientNorm (Syn.shift C)) (natCode (Syn.shift A)) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [factorBounds,Syn.shift,GaussianRationalPolynomialPowers.subst_table,PTm.subst_zero] using
    RationalArgmin.rationalLE_congr
      (coefficientNorm_congr (GaussianRationalPolynomialPowers.factor_original (Syn.shift C) (Syn.shift K) (var 0) Prf.hyp0)).eqSymm
      (.eqRefl _) hs.wk

theorem repeated_factor_differences (C D N K E : PTm n)
    (h : Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D (succ N))) E) : Γ ⊢[PRAAx]
    factorDifferences (table C K) (table D K) K N zero E := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients (Syn.shift C) (Syn.shift D) (succ (Syn.shift N)))) (Syn.shift E) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have codes := subCoefficients_congr (Γ := Δ)
    (GaussianRationalPolynomialPowers.factor_original (Syn.shift C) (Syn.shift K) (var 0) Prf.hyp0)
    (GaussianRationalPolynomialPowers.factor_original (Syn.shift D) (Syn.shift K) (var 0) Prf.hyp0) (.eqRefl (succ (Syn.shift N)))
  simpa only [Δ,factorDifferences,GaussianPolynomialDeterminantStageError.factorDifference,Syn.shift,
    GaussianRationalPolynomialPowers.subst_table,PTm.subst_zero] using
      RationalArgmin.rationalLE_congr (coefficientNorm_congr codes).eqSymm (.eqRefl _) hs.wk

theorem original_power_norm (C N K A j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode A)) (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (powerPrefix C N K j)) (natCode (pw A j)) :=
  GaussianPolynomialDeterminantStageNorm.stage_norm _ _ _ _ _ _
    (GaussianRationalPolynomialPowers.table_shape C N K hC) (repeated_factor_bounds C K A hA) hj

theorem original_power_variation (C D N K A E j : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode A))
    (hB : Γ ⊢[PRAAx] rationalLE (coefficientNorm D) (natCode A))
    (hE : Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D (succ N))) E)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (powerPrefix C N K j) (powerPrefix D N K j) (succ (j*N))))
      (RationalArithmetic.multiply (natCode (budget A one j)) E) :=
  GaussianPolynomialDeterminantStageError.stage_error _ _ _ _ _ _ _ _
    (GaussianRationalPolynomialPowers.table_shape C N K hC) (GaussianRationalPolynomialPowers.table_shape D N K hD)
    (repeated_factor_bounds C K A hA) (repeated_factor_bounds D K A hB) (repeated_factor_differences C D N K E hE) hj

theorem original_actual_power_coefficient_norm_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 2) ⟶
      rationalLE (coefficientNorm (var 0)) (natCode (var 4)) ⟶ rationalLE (coefficientNorm (var 1)) (natCode (var 4)) ⟶
      rationalLE (coefficientNorm (subCoefficients (var 0) (var 1) (succ (var 2)))) (var 5) ⟶ le (var 6) (var 3) ⟶
      rationalLE (coefficientNorm (subCoefficients (powerPrefix (var 0) (var 2) (var 3) (var 6))
        (powerPrefix (var 1) (var 2) (var 3) (var 6)) (succ (var 6*var 2))))
        (RationalArithmetic.multiply (natCode (budget (var 4) one (var 6))) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (original_power_variation _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialPowerNormVariation
