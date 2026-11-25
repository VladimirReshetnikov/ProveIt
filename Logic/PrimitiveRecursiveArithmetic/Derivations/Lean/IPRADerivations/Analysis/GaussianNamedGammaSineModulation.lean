import IPRADerivations.Analysis.GaussianArctangentExponentialPeriod
import IPRADerivations.Analysis.GaussianEulerNamedIBPRecurrence
import IPRADerivations.Analysis.GaussianGammaFactorialValues
import IPRADerivations.Analysis.GaussianNamedGammaFirstCrossing
import IPRADerivations.Analysis.GaussianRealNameExponentialInjectivity

/-!
# Modulating the original named Gamma by an exponential

The coefficient and sine value are named Gaussian points. The derived
exponential uses the disk returned by the actual product name. Sine
periodicity then lifts the original Gamma recurrence, and zero and unit
sine values give the factorial and nonuniqueness conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaSineModulation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianExponentialRadiusIndependence (independent_radii_proper)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF zeroF one_fast zero_fast zero_at multiply_one multiply_one_left multiply_associative multiply_commutative)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalReciprocal (qone)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentF (c s : PR 2) : PR 2 := multiplyF c s
def exponentData (c s : PR 2) (a y : PTm n) : PTm n := multiplyData c s a y
def factorF (c s : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (exponentF c s)
def factorData (c s : PR 2) (a y : PTm n) : PTm n :=
  let w := exponentData c s a y
  GaussianRadiusExponentialName.data (GaussianNameBounds.U (exponentF c s) w) w
def valueF (g c s : PR 2) : PR 2 := multiplyF g (factorF c s)
def valueData (g c s : PR 2) (x a y : PTm n) : PTm n := multiplyData g (factorF c s) x (factorData c s a y)

theorem exponent_regular (c s : PR 2) (a y : PTm n)
    (hc : Γ ⊢[PRAAx] pointCN c a) (hs : Γ ⊢[PRAAx] pointCN s y) :
    Γ ⊢[PRAAx] pointCN (exponentF c s) (exponentData c s a y) :=
  multiply_fast c s a y hc hs

theorem factor_regular (c s : PR 2) (a y : PTm n)
    (hc : Γ ⊢[PRAAx] pointCN c a) (hs : Γ ⊢[PRAAx] pointCN s y) :
    Γ ⊢[PRAAx] pointCN (factorF c s) (factorData c s a y) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (exponent_regular c s a y hc hs))

theorem value_regular (g c s : PR 2) (x a y : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g x) (hc : Γ ⊢[PRAAx] pointCN c a) (hs : Γ ⊢[PRAAx] pointCN s y) :
    Γ ⊢[PRAAx] pointCN (valueF g c s) (valueData g c s x a y) :=
  multiply_fast _ _ _ _ hg (factor_regular c s a y hc hs)

theorem factor_proper (c s t : PR 2) (a y z : PTm n) (hc : Γ ⊢[PRAAx] pointCN c a)
    (hs : Γ ⊢[PRAAx] pointCN s y) (ht : Γ ⊢[PRAAx] pointCN t z) (he : Γ ⊢[PRAAx] crossEquivalent s t y z) :
    Γ ⊢[PRAAx] crossEquivalent (factorF c s) (factorF c t) (factorData c s a y) (factorData c t a z) :=
  independent_radii_proper _ _ _ _ _ _ (exponential_input _ _ (exponent_regular c s a y hc hs))
    (exponential_input _ _ (exponent_regular c t a z hc ht))
    (multiply_cross c c s t a a y z hc hc hs ht (cross_refl _ _ hc) he)

theorem product_constant_one (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f constantF) f (multiplyData f constantF x qone) x := by
  have e := GaussianArctangentExponentialPeriod.constant_one_cross (Γ := Γ) x
  have mid := multiply_cross f f constantF oneF x x qone x hx hx (constant_regular _) (one_fast x)
    (cross_refl _ _ hx) e
  exact cross_trans _ _ _ _ _ _ mid (multiply_one _ _ hx)

private theorem product_constant_zero (f : PR 2) (x anchor : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f constantF) zeroF (multiplyData f constantF x qzero) anchor := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (multiply_fast f constantF x qzero hx (constant_regular _)) (zero_fast anchor)
  refine .allI ?_
  let y := Syn.shift x
  let p : PTm (n+1) := var 0
  have e : Γ.map Fm.shift ⊢[PRAAx] ap2 (multiplyF f constantF) p (multiplyData f constantF y qzero) ≐ qzero :=
    (GaussianNameArithmetic.multiply_at f constantF y qzero p).eqTrans
      ((GaussianNameArithmetic.recode_congr ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
          (constant_at _ _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (GaussianRationalSyntheticDivision.qzero_canonical)))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,y,p,
    GaussianNameArithmetic.subst_multiplyData,GaussianRationalHorner.subst_qzero] using
    e.eqTrans (zero_at p (Syn.shift anchor)).eqSymm

theorem factor_at_zero (c s : PR 2) (a y x : PTm n)
    (hc : Γ ⊢[PRAAx] pointCN c a) (hs : Γ ⊢[PRAAx] pointCN s y)
    (he : Γ ⊢[PRAAx] crossEquivalent s constantF y qzero) :
    Γ ⊢[PRAAx] crossEquivalent (factorF c s) oneF (factorData c s a y) x := by
  have mid := factor_proper c s constantF a y qzero hc hs (constant_regular _) he
  have exp := independent_radii_proper (exponentF c constantF) zeroF _ one
    (exponentData c constantF a qzero) x
    (exponential_input _ _ (exponent_regular _ _ _ _ hc (constant_regular _)))
    (GaussianExponentialInverse.zero_input _ _) (product_constant_zero c a x hc)
  exact cross_trans _ _ _ _ _ _ mid
    (cross_trans _ _ _ _ _ _ exp (GaussianExponentialInverse.zero_exponential_cross one x))

theorem factor_at_one (c s : PR 2) (a y R : PTm n)
    (hc : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input c R a) (hs : Γ ⊢[PRAAx] pointCN s y)
    (he : Γ ⊢[PRAAx] crossEquivalent s constantF y qone) :
    Γ ⊢[PRAAx] crossEquivalent (factorF c s) (GaussianRadiusExponentialName.nameF c)
      (factorData c s a y) (GaussianRadiusExponentialName.data R a) := by
  have mid := factor_proper c s constantF a y qone hc.andE₁ hs (constant_regular _) he
  have exp := independent_radii_proper _ c _ R _ a
    (exponential_input _ _ (exponent_regular c constantF a qone hc.andE₁ (constant_regular _)))
    hc (product_constant_one c a hc.andE₁)
  exact cross_trans _ _ _ _ _ _ mid exp

theorem value_at_zero (g c s : PR 2) (x a y : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g x) (hc : Γ ⊢[PRAAx] pointCN c a) (hs : Γ ⊢[PRAAx] pointCN s y)
    (he : Γ ⊢[PRAAx] crossEquivalent s constantF y qzero) :
    Γ ⊢[PRAAx] crossEquivalent (valueF g c s) g (valueData g c s x a y) x :=
  cross_trans _ _ _ _ _ _
    (multiply_cross g g (factorF c s) oneF x x _ x hg hg (factor_regular c s a y hc hs) (one_fast x)
      (cross_refl _ _ hg) (factor_at_zero c s a y x hc hs he))
    (multiply_one g x hg)

/-- The original recurrence persists whenever the two sine values agree. -/
theorem recurrence_of_sine_period (f c s t : PR 2) (x A a y z : PTm n)
    (hg : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A)
    (hc : Γ ⊢[PRAAx] pointCN c a)
    (hs : Γ ⊢[PRAAx] pointCN s y) (ht : Γ ⊢[PRAAx] pointCN t z)
    (he : Γ ⊢[PRAAx] crossEquivalent t s z y) : Γ ⊢[PRAAx]
    crossEquivalent (valueF (GaussianNamedGamma.nameF (shiftF f)) c t)
      (multiplyF f (valueF (GaussianNamedGamma.nameF f) c s))
      (valueData (GaussianNamedGamma.nameF (shiftF f)) c t (GaussianNamedGamma.data (shiftData x) A) a z)
      (multiplyData f (valueF (GaussianNamedGamma.nameF f) c s) x
        (valueData (GaussianNamedGamma.nameF f) c s (GaussianNamedGamma.data x A) a y)) := by
  let G := GaussianNamedGamma.nameF f
  let g := GaussianNamedGamma.data x A
  let G' := GaussianNamedGamma.nameF (shiftF f)
  let g' := GaussianNamedGamma.data (shiftData x) A
  let P := GaussianEulerNamedIBPRecurrence.productF f
  let p := GaussianEulerNamedIBPRecurrence.productData f x A
  have regular := GaussianNamedGamma.name_regular f x A hg
  have shifted := GaussianNamedGamma.name_regular _ _ _ (GaussianEulerNamedShiftInput.original_source f x A hg)
  have rf := factor_regular c s a y hc hs
  have first := multiply_cross G' P (factorF c t) (factorF c s) g' p _ _ shifted
    (multiply_fast f G x g hg.andE₁ regular) (factor_regular c t a z hc ht) rf
    (GaussianEulerNamedIBPRecurrence.original_named_Gamma_IBP_recurrence f x A hg)
    (factor_proper c t s a z y hc ht hs he)
  exact cross_trans _ _ _ _ _ _ first
    (multiply_associative f G (factorF c s) x g (factorData c s a y) hg.andE₁ regular rf)

theorem factorial_of_sine_zero (c s : PR 2) (i a y : PTm n)
    (hc : Γ ⊢[PRAAx] pointCN c a) (hs : Γ ⊢[PRAAx] pointCN s y)
    (he : Γ ⊢[PRAAx] crossEquivalent s constantF y qzero) :
    Γ ⊢[PRAAx] crossEquivalent (valueF GaussianGammaReciprocalInverse.gammaF c s) constantF
      (valueData GaussianGammaReciprocalInverse.gammaF c s (GaussianGammaFactorialValues.data i) a y)
      (GaussianGammaFactorialValues.factorialValue i) :=
  cross_trans _ _ _ _ _ _
    (value_at_zero _ _ _ _ _ _ (GaussianGammaFactorialValues.value_regular i) hc hs he)
    (GaussianGammaFactorialValues.original_C21_factorial i)

private theorem zero_axis (x : PTm n) :
    Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples zeroF x := by
  refine .allI ?_
  exact RationalGaussianEmbedding.axis_congr (zero_at (var 0) (Syn.shift x)).eqSymm
    RationalGaussianEmbedding.axis_zero

private theorem zero_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF constantF x qzero := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast x) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_qzero] using
    (zero_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans
      (constant_at (var 0) (qzero : PTm (n+1))).eqSymm

/-- At a unit sine value, equality with a nonzero original Gamma would force
the real modulation coefficient to vanish. -/
theorem coefficient_zero_of_value_agreement (g c s : PR 2) (x a y R A : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g x) (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart g A x)
    (hc : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input c R a)
    (hr : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples c a)
    (hs : Γ ⊢[PRAAx] pointCN s y) (he : Γ ⊢[PRAAx] crossEquivalent s constantF y qone)
    (h : Γ ⊢[PRAAx] crossEquivalent (valueF g c s) g (valueData g c s x a y) x) :
    Γ ⊢[PRAAx] crossEquivalent c constantF a qzero := by
  let e := GaussianRadiusExponentialName.data R a
  let E := GaussianRadiusExponentialName.nameF c
  have heReg := GaussianRadiusExponentialName.name_regular c R a hc
  have scaled := multiply_cross g g (factorF c s) E x x _ e hg hg
    (factor_regular c s a y hc.andE₁ hs) heReg (cross_refl _ _ hg) (factor_at_one c s a y R hc hs he)
  have reverse := multiply_commutative E g e x heReg hg
  have remove := cross_symm _ _ _ _ (multiply_one_left g x hg)
  have productEqual := cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ reverse (cross_symm _ _ _ _ scaled))
    (cross_trans _ _ _ _ _ _ h remove)
  have expOne := GaussianNamedGammaFirstCrossing.cancel_right E oneF g e x x A heReg (one_fast x) hg ha productEqual
  have hz := GaussianExponentialInverse.zero_input (Γ := Γ) R x
  have equalExp := cross_trans _ _ _ _ _ _ expOne
    (cross_symm _ _ _ _ (GaussianExponentialInverse.zero_exponential_cross R x))
  exact cross_trans _ _ _ _ _ _
    (GaussianRealNameExponentialInjectivity.original_injective c zeroF R a x
      (.andI (.andI hc hz) (.andI hr (zero_axis x))) equalExp) (zero_constant x)

end LeanProofs.IPRA.Analysis.GaussianNamedGammaSineModulation
