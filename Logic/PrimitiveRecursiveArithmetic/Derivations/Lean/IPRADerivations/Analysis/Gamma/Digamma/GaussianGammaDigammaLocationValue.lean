import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaPositiveStationary
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLocationInput
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLocationInterior
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaFirstCrossing

/-!
# The actual digamma value at the completed positive location

At the regular dyadic location, the original named Gamma value is
uniformly apart from zero. Form the quotient of the actual first
logarithmic Euler integral by this Gamma value with the named
reciprocal and normalized product. Its value is exactly zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaDigammaDyadicLocation (locationF)
open GaussianGammaDigammaLocationInput (named_source named_real_source)
open GaussianGammaDigammaPositiveStationary (original_integral_zero)
open GaussianGammaCanonicalExponent (constantF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianNameArithmetic (multiplyData multiplyF multiply_fast multiply_at recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (zeroF zero_at zero_fast)
open GaussianNamedGammaFirstCrossing (inverseClock positive_gamma_apart)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left qzero_canonical)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "GF" => GaussianNamedGamma.nameF locationF
local notation "LF" => GaussianNamedEulerLogarithmicImproper.nameF locationF
local notation "RF" => GaussianNameReciprocal.nameF GF

def derivativeData (x : PTm n) : PTm n := GaussianNamedEulerLogarithmicImproper.data one x one
def inverseData (x : PTm n) : PTm n := GaussianNameReciprocal.nameData inverseClock (GaussianNamedGamma.data x one)
def nameF : PR 2 := multiplyF LF RF
def data (x : PTm n) : PTm n := multiplyData LF RF (derivativeData x) (inverseData x)

theorem reciprocal_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN RF (inverseData x) :=
  GaussianNameReciprocal.name_fast GF inverseClock (GaussianNamedGamma.data x one)
    (GaussianNamedGamma.name_regular locationF x one (named_source x))
    (positive_gamma_apart locationF x one (named_real_source x))

theorem name_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data x) :=
  multiply_fast LF RF _ _
    (GaussianNamedEulerLogarithmicImproper.name_regular locationF one x one (named_source x))
    (reciprocal_regular x)

private theorem zero_product (f : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] pointCN f y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF zeroF f) zeroF (multiplyData zeroF f x y) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (multiply_fast _ _ _ _ (zero_fast x) h) (zero_fast x)
  refine .allI ?_
  let a := Syn.shift x
  let b := Syn.shift y
  let p : PTm (n+1) := var 0
  have e : Γ.map Fm.shift ⊢[PRAAx] ap2 (multiplyF zeroF f) p (multiplyData zeroF f a b) ≐ qzero :=
    (multiply_at zeroF f a b p).eqTrans
      ((recode_congr ((qmul_congr (zero_at _ _) (.eqRefl _)).eqTrans (qmul_zero_left _))).eqTrans
        (GaussianExponentialReference.recode_fixed _ qzero_canonical))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,a,b,p,GaussianNameArithmetic.subst_multiplyData]
    using e.eqTrans (zero_at p a).eqSymm

theorem original_digamma_zero (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF zeroF (data x) x := by
  have h := reciprocal_regular (Γ := Γ) x
  have derivative := GaussianNamedEulerLogarithmicImproper.name_regular locationF one x one (named_source (Γ := Γ) x)
  have replaced := multiply_cross LF zeroF RF RF (derivativeData x) x (inverseData x) (inverseData x)
    derivative (zero_fast x) h h (original_integral_zero x) (cross_refl _ _ h)
  exact cross_trans _ _ _ _ _ _ replaced (zero_product RF x (inverseData x) h)

theorem actual_positive_location_digamma_zero_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (crossEquivalent nameF zeroF (data (var 0)) (var 0)) :=
  closeUniv 1 (original_digamma_zero _)

theorem actual_positive_digamma_zero_and_interior_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      ((strictOrder constantF locationF (fraction one one) (var 0) ⋏
        strictOrder locationF constantF (var 0) (fraction two one)) ⋏
        crossEquivalent nameF zeroF (data (var 0)) (var 0)) :=
  closeUniv 1 (.andI (GaussianGammaDigammaLocationInterior.strict_interior _) (original_digamma_zero _))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationValue
