import IPRADerivations.Analysis.GaussianNamedSineTaylor
import IPRADerivations.Analysis.GaussianNameRingLaws

/-!
# The original imaginary sine input as multiplication by (i)

The pointwise rotation used by sine agrees with multiplication of
regular names by the constant Gaussian rational (i).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedImaginaryProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope multiply_sample_error)
open GaussianNamedSineTaylor (imaginaryF imaginary_at imaginary_regular imaginaryArgument)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCoefficientNameBounds (unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem ordinary_product (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (imaginaryF f) (multiplyF constantF f) x
      (multiplyData constantF f imaginaryPoint x) := by
  apply equivalent_of_envelope _ _ _ _ (multiplyModulus constantF f imaginaryPoint x+one)
    (imaginary_regular f x h) (multiply_fast _ _ _ _ (constant_regular _) h)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let y := Syn.shift x
  let p : PTm (n+1) := var 0
  have hy : Δ ⊢[PRAAx] pointCN f y := by simpa only [Fm.shift,Syn.shift,subst_pointCN,Δ,y] using h.shift
  have e := imaginary_at (Γ := Δ) f p y
  have c := constant_at (Γ := Δ) p imaginaryPoint
  have raw := multiply_sample_error constantF f imaginaryPoint y p (constant_regular _) hy
  have v := (qmul_congr c (.eqRefl (ap2 f p y))).eqTrans e.eqSymm
  have estimate := distance_symmetric _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) v (.eqRefl _) (.eqRefl _) raw)
  simpa only [Δ,y,p,Syn.shift,GaussianNameArithmetic.subst_multiplyData,
    GaussianNameArithmetic.subst_multiplyModulus,PTm.subst_add,GaussianRationalHorner.subst_ofGaussian,
    imaginaryPoint,imaginaryCode,ComplexLogarithmRemainder.subst_code,ZT.subst_ofNat,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using estimate

theorem original_sine_rotation_product_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (imaginaryF f) (multiplyF constantF f) (var 0)
      (multiplyData constantF f imaginaryPoint (var 0))) :=
  closeUniv 1 (.impI (ordinary_product f _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedImaginaryProduct
