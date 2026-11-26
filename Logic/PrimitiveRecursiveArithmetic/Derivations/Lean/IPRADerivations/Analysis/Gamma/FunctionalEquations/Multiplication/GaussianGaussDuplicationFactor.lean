import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferencePrefix
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSqrtPi
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductAppend
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues
import IPRADerivations.Core.Evaluation

/-!
# The exact normalization factor at Gauss order two

The original reference product consists of Gamma(1/2) and Gamma(1).
The first is selected by a singleton fold and agrees with the
original bounded square-root name for pi.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussDuplicationFactor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianGammaFactorialValues (gamma_fields_congr)
open GaussianGammaGaussReferencePrefix (full_prefix_cross prefix_bounds prefix_regular)
open GaussianGammaGaussReferenceProduct (argument rowF row_at rowRadius nameF data)
open GaussianGammaHalfSquareLimit (gammaHalf)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedFiniteProductAppend (lastRow singleton_cross)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem native_one :
    Γ ⊢[PRAAx] argument (zero : PTm n) ≐ oneCode := by
  let v := PTm.ev Fin.elim0 (oneCode : PTm 0)
  have h := eval_ground (Γ := Γ) (argument (zero : PTm 0)) v (by decide)
  have k := eval_ground (Γ := Γ) (oneCode : PTm 0) v rfl
  simpa [argument,scale,oneCode,one] using h.eqTrans k.eqSymm

theorem first_reference_at (p : PTm n) :
    Γ ⊢[PRAAx] ap3 rowF p zero two ≐ ap2 gammaF p gammaHalf :=
  (row_at p zero two).eqTrans
    (congrAp2 gammaF (.eqRefl p) (gamma_fields_congr native_one (.eqRefl _) (.eqRefl _) (.eqRefl _)))

theorem reference_half :
    Γ ⊢[PRAAx] crossEquivalent nameF gammaF (data two) (gammaHalf : PTm n) := by
  have row : Γ ⊢[PRAAx] lastRow rowF gammaF zero two gammaHalf := by
    refine .allI ?_
    simpa [lastRow,Syn.shift,gammaHalf,one,two] using first_reference_at (Γ := Γ.map Fm.shift) (var 0)
  have half := GaussianGammaHalfSquareLimit.gamma_regular (Γ := Γ)
  exact cross_trans _ _ _ _ _ _ (full_prefix_cross (one : PTm n))
    (singleton_cross rowF gammaF (rowRadius two) one two gammaHalf (prefix_bounds one) (prefix_regular one) half row)

theorem reference_sqrt_pi (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianGammaHalfSqrtPi.nameF (data two) x :=
  cross_trans _ _ _ _ _ _ reference_half (GaussianGammaHalfSqrtPi.original_half_is_sqrt_pi x)

theorem actual_Gauss_duplication_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent nameF GaussianGammaHalfSqrtPi.nameF (data two) (var 0)) :=
  closeUniv 1 (reference_sqrt_pi _)

end LeanProofs.IPRA.Analysis.GaussianGaussDuplicationFactor
