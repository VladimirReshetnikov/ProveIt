import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialAddition

/-!
# Logarithm of an exact positive rational multiple

The checked exponential recovers the named positive argument.
The exponential addition law and its real injectivity then give
the logarithm law at the original programs and their own clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmScale

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedPositiveLogarithm (source)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRealNameExponentialInjectivity (axisSamples axis_sample_at independent_radii_injective)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "logData" => GaussianPositiveRationalLogarithm.data
local notation "namedLogF" => GaussianNamedPositiveLogarithm.nameF
local notation "namedLogData" => GaussianNamedPositiveLogarithm.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ep" => GaussianRadiusExponentialName.data
local notation "logRadius" => GaussianCompactLogarithmBounds.radius

theorem sum_axis (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] axisSamples f x) (hg : Γ ⊢[PRAAx] axisSamples g y) :
    Γ ⊢[PRAAx] axisSamples (addF f g) (addData x y) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let x' := Syn.shift x
  let y' := Syn.shift y
  let t : PTm (n+1) := GaussianFastValueCut.exponent two (var 0)
  have fs : Δ ⊢[PRAAx] axisSamples f x' := by
    simpa only [Δ,x',Fm.shift,Syn.shift,GaussianRealNameExponentialInjectivity.subst_axisSamples] using hf.shift
  have gs : Δ ⊢[PRAAx] axisSamples g y' := by
    simpa only [Δ,y',Fm.shift,Syn.shift,GaussianRealNameExponentialInjectivity.subst_axisSamples] using hg.shift
  have e := (GaussianNameArithmetic.add_at (Γ := Δ) f g x' y' (var 0)).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  have ax := RationalGaussianEmbedding.axis_congr e.eqSymm
    (RationalGaussianEmbedding.axis_add _ _ (axis_sample_at f x' t fs) (axis_sample_at g y' t gs))
  simpa only [GaussianNameArithmetic.subst_addData,Δ,x',y',Syn.shift] using ax

theorem exact_rational_axis (a b : PTm n) : Γ ⊢[PRAAx] axisSamples logF (logData a b) := by
  refine .allI ?_
  simpa only [axisSamples,Syn.shift,GaussianPositiveRationalLogarithm.subst_data,GaussianPositiveRationalLogarithm.sample]
    using GaussianPositiveRationalLogarithm.sample_axis (Γ := Γ.map Fm.shift) (var 0) (Syn.shift a) (Syn.shift b)

theorem logarithm_scale (f g : PR 2) (a b x y P T Q W : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hf : Γ ⊢[PRAAx] source f x P T) (hg : Γ ⊢[PRAAx] source g y Q W)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF f) g (multiplyData constantF f (fraction a b) x) y) :
    Γ ⊢[PRAAx] crossEquivalent (namedLogF g) (addF logF (namedLogF f)) (namedLogData y Q)
      (addData (logData a b) (namedLogData x P)) := by
  let F := namedLogF f
  let G := namedLogF g
  let X := namedLogData x P
  let Y := namedLogData y Q
  let V := logData a b
  let S := GaussianPositiveRationalLogarithm.radius a b
  let U := logRadius P T
  let R := S+U+one
  have li := GaussianPositiveRationalLogarithm.exponential_input a b h
  have fi := GaussianNamedPositiveLogarithm.exponential_input f x P T hf
  have gi := GaussianNamedPositiveLogarithm.exponential_input g y Q W hg
  have leR : Γ ⊢[PRAAx] le one R := le_add_left _ _
  have lR := GaussianExponentialRadiusIndependence.input_widen logF S R V li
    (le_trans (le_add_right S U) (le_add_right _ _))
  have fR := GaussianExponentialRadiusIndependence.input_widen F U R X fi
    (le_trans (le_add_left U S) (le_add_right _ _))
  have logOut := cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross logF R S V lR li)
    (GaussianPositiveRationalLogarithm.exponential_fraction a b h)
  have gammaOut := cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross F R U X fR fi)
    (GaussianNamedPositiveLogarithmExponential.original_recovery f x P T hf)
  have left := GaussianGammaAdjacentCutoff.multiply_cross (E logF) constantF (E F) f (ep R V) (fraction a b) (ep R X) x
    (GaussianRadiusExponentialName.name_regular logF R V lR) (constant_regular _)
    (GaussianRadiusExponentialName.name_regular F R X fR) hf.andE₁ logOut gammaOut
  have recover := GaussianNamedPositiveLogarithmExponential.original_recovery g y Q W hg
  have expAdd := GaussianExponentialAddition.exponential_add_cross logF F R V X leR lR fR
  have e := cross_trans _ _ _ _ _ _ recover (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ he)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left) expAdd))
  exact independent_radii_injective G (addF logF F) (logRadius Q W) (R+R) Y (addData V X)
    gi (GaussianExponentialReference.add_input logF F R V X lR fR)
    (GaussianNamedPositiveLogarithm.real_samples g y Q)
    (sum_axis logF F V X (exact_rational_axis a b) (GaussianNamedPositiveLogarithm.real_samples f x P)) e

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmScale
