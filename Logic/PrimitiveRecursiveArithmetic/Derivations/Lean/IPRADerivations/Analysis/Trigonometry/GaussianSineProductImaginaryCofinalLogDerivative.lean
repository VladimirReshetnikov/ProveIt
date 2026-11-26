import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryCoshIdentity
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryDerivativeComparison
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryHyperbolicProductRule
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaFirstCrossing
import IPRADerivations.Analysis.Trigonometry.GaussianSineReflectionLower

/-!
# Exact cofinal logarithmic derivative of the imaginary-axis sine product

The two checked quadratic first-order rates for the same original
hyperbolic sine give exact agreement of their derivative names. The
nonzero original π factor cancels, leaving the actual identity
`cosh(πx) = P(x) + x·P(x)·Σ 2x/(j²+x²)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCofinalLogDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedConstantProductName (constant_regular)
open GaussianNameArithmetic (add_fast multiply_fast)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (multiply_commutative)
open GaussianSineProductImaginaryCoshIdentity (coshF coshData cosh_regular derivative_as_pi_cosh)
open GaussianSineProductImaginaryDerivativeComparison (productFamily productRate scale scaled_source)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "ExpDerivative" => GaussianSineProductImaginaryHyperbolicDerivative.derivativeF
local notation "expDerivativeData" => GaussianSineProductImaginaryHyperbolicDerivative.derivativeData
local notation "ProdDerivative" => GaussianSineProductImaginaryHyperbolicProductRule.derivativeF
local notation "prodDerivativeData" => GaussianSineProductImaginaryHyperbolicProductRule.derivativeData
local notation "coefficient" => GaussianSineProductImaginaryHyperbolicProductRule.coefficient
local notation "sumF" => GaussianSineProductImaginaryHyperbolicProductRule.sumF
local notation "sumData" => GaussianSineProductImaginaryHyperbolicProductRule.sumData

theorem fixed_base_dyadic_rate (A B R x : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le (A+one) (R*B)) :
    Γ ⊢[PRAAx] productFamily ProdDerivative (prodDerivativeData A B R x) A B R x (coefficient R x) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  let k := scale (sh x) (var 0)
  have rs : Δ ⊢[PRAAx] le one (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hR.shift
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have as' : Δ ⊢[PRAAx] le (sh A+one) (sh R*sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hA.shift
  have h := scaled_source (sh A) (sh B) (sh R) (sh x) (var 0) rs bs as'
  have rate : Δ ⊢[PRAAx] productRate ProdDerivative (prodDerivativeData (sh A) (sh B) (sh R) (sh x))
      (sh A) (sh B) k (sh R) (sh x) (coefficient (sh R) (sh x)) :=
    GaussianSineProductImaginaryHyperbolicProductRule.scaled_unit_rate (sh A) (sh B) k (sh R) (sh x) bs
      h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁
  simpa only [productFamily,Δ,sh,k,Syn.shift,GaussianSineProductImaginaryHyperbolicProductRule.subst_derivativeData,
    GaussianSineProductImaginaryHyperbolicProductRule.subst_coefficient] using rate

theorem derivatives_equal (A B R x : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le (A+one) (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent ExpDerivative ProdDerivative (expDerivativeData A B R x) (prodDerivativeData A B R x) :=
  GaussianSineProductImaginaryDerivativeComparison.equal_derivatives ProdDerivative (prodDerivativeData A B R x)
    A B R x (coefficient R x) hR hB hA
    (GaussianSineProductImaginaryHyperbolicProductRule.derivative_regular A B R x hB (le_trans (le_add_right _ _) hA))
    (fixed_base_dyadic_rate A B R x hR hB hA)

theorem pi_apart (x : PTm n) : Γ ⊢[PRAAx] GaussianNameReciprocal.apart Pi zero x := by
  let p := GaussianNameReciprocal.anchor (zero : PTm n)
  let q := ap2 Pi p x
  have a := GaussianSineReflectionLower.original_pi_sample_lower (Γ := Γ) p x
  have b := GaussianRationalLowerBounds.name_lower q two one (le_succ_self one) (le_refl one) a
  exact GaussianNameReciprocal.lower_congr (.eqRefl q) (pw_zero two).eqSymm b

theorem cosh_as_product_and_derivative (A B R x : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le (A+one) (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent coshF sumF (coshData A B R x) (sumData A B R) := by
  let u := coshData A B R x
  let v := sumData A B R
  have ha := le_trans (le_add_right A one) hA
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hu := cosh_regular A B R x hB ha
  have hv : Γ ⊢[PRAAx] pointCN sumF v := add_fast _ _ _ _
    (GaussianSineProductName.name_regular _ _ _ hB (GaussianSineProductImaginaryFirstOrderBound.axis_disk A B R ha))
    (multiply_fast _ _ _ _ (constant_regular (GaussianSineProductImaginaryLogDerivative.rationalReal A B))
      (GaussianSineProductImaginaryCofinalDerivative.derivative_regular A B R hB ha))
  have e := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (derivative_as_pi_cosh A B R x hB ha))
    (derivatives_equal A B R x hR hB hA)
  have swap := cross_trans _ _ _ _ _ _ (multiply_commutative coshF Pi u x hu hp)
    (cross_trans _ _ _ _ _ _ e (multiply_commutative Pi sumF x v hp hv))
  exact GaussianNamedGammaFirstCrossing.cancel_right coshF sumF Pi u v x zero hu hv hp (pi_apart x) swap

theorem actual_cofinal_hyperbolic_logarithmic_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 2) ⋏ (le one (var 1) ⋏ le (var 0+one) (var 2*var 1))) ⟶
        crossEquivalent coshF sumF (coshData (var 0) (var 1) (var 2) (var 3)) (sumData (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (cosh_as_product_and_derivative _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCofinalLogDerivative
