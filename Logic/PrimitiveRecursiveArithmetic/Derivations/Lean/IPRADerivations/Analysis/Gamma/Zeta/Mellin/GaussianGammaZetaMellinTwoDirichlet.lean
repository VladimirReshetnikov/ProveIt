import IPRADerivations.Analysis.Gamma.Zeta.Mellin.GaussianGammaZetaMellinIdentity
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitNormalization
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues
import IPRADerivations.Analysis.Gamma.GaussianGammaInputProperness
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# The original Gamma–zeta Mellin identity at two

The zero-starting integer trajectory for Gamma reaches the Mellin
chart at its first successor. Its checked factorial value is one,
so the original specialized Mellin sampler equals the original
cofinal Dirichlet sampler.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinTwoDirichlet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaFactorialValues (argument factorialValue integer_source natural_congr natural_one)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_symm cross_trans diagonal_refl)
open GaussianNameRingLaws (oneF one_at one_fast multiply_one)
open GaussianNameArithmetic (multiply_equivalent)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianGammaZetaMellinImproper.nameF
local notation "Z" => GaussianGammaZetaDirichletCofinal.nameF
local notation "P" => GaussianGammaZetaDirichletProduct.nameF

def mellinData : PTm n := GaussianGammaZetaMellinImproper.data oneCode one one zero
def dirichletData : PTm n := GaussianGammaZetaDirichletCofinal.data oneCode one one one

theorem source_at_two : Γ ⊢[PRAAx]
    GaussianEulerIntegralGammaIdentification.source (oneCode : PTm n) one one one :=
  .andI GaussianEulerUnitNormalization.unit_lower_source (le_refl one)

private theorem first_factorial : Γ ⊢[PRAAx] factorialValue (one : PTm n) ≐ qone :=
  (natural_congr ((fact_succ zero zero).eqTrans
    ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul one)))).eqTrans natural_one

private theorem first_factorial_name (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent constantF oneF (factorialValue one) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianGammaFactorialValues.subst_factorialValue,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) (factorialValue (one : PTm (n+1)))).eqTrans
      (first_factorial.eqTrans (one_at (var 0) (Syn.shift x)).eqSymm)

theorem gamma_at_two (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent gammaF oneF
    (GaussianGammaZetaDirichletProduct.actualGammaData oneCode one one one) x := by
  have same := GaussianGammaInputProperness.original_Gamma_proper (Γ := Γ) (argument one) (shifted oneCode one)
    (one+one) one one one (integer_source one) (GaussianGammaShiftTrajectory.point_native oneCode one one)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ same) (cross_trans _ _ _ _ _ _
    (GaussianGammaFactorialValues.original_C21_factorial one) (first_factorial_name x))

theorem original_mellin_two_is_dirichlet : Γ ⊢[PRAAx] crossEquivalent I Z (mellinData : PTm n) dirichletData := by
  let x : PTm n := dirichletData
  let g : PTm n := GaussianGammaZetaDirichletProduct.actualGammaData oneCode one one one
  have hZ := GaussianGammaZetaDirichletCofinal.regular (Γ := Γ) oneCode one one one source_at_two
  have hg := GaussianEulerIntegralGammaIdentification.original_gamma_regular (Γ := Γ) (shifted oneCode one) (one+one) one one
    (GaussianGammaZetaDirichletPowerOrder.shifted_source oneCode one one one source_at_two)
  have product := multiply_equivalent Z Z gammaF oneF x x g x hZ hZ hg (one_fast x) (diagonal_refl Z x)
    (cross_to_diagonal _ _ _ _ (gamma_at_two x))
  exact cross_trans I P Z mellinData _ dirichletData
    (GaussianGammaZetaMellinIdentity.equivalent oneCode one one zero source_at_two)
    (cross_trans _ _ _ _ _ _ product (multiply_one Z x hZ))

theorem actual_original_Mellin_at_two_is_Dirichlet_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent I Z mellinData dirichletData :=
  original_mellin_two_is_dirichlet

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinTwoDirichlet
