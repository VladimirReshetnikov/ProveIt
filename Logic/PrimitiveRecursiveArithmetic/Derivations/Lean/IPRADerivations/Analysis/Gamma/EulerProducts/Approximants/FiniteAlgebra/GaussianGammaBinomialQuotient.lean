import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.FiniteAlgebra.GaussianGammaBinomialCleared

/-!
# V9 with the actual original Gamma quotient frontend

Both original Gamma endpoints have their own pole certificates. The
denominator's actual named reciprocal receives a computed apartness
anchor from its bounded original C7 inverse. The literal finite binomial
polynomial is the value of Gamma(z+1)/(N! Gamma(z-N+1)).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaBinomialQuotient

open_ipra
open GaussianGammaFallingFactorial (start baseRadius endpointRadius fallingProduct factorialInverse binomial)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular gamma_product)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianNameRingLaws (oneF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF

def input (z R B a d e f N : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  ((le one a ⋏ (le one d ⋏ GaussianGammaEulerHeadLower.poleGuard (start z B N) B a d (two*baseRadius R N))) ⋏
    (le one e ⋏ (le one f ⋏ GaussianGammaEulerHeadLower.poleGuard (shifted z B) B e f (two*endpointRadius R N))))
def baseGammaData (z R B d N : PTm n) : PTm n := gammaData (start z B N) (baseRadius R N) B d
def topGammaData (z R B f N : PTm n) : PTm n := gammaData (shifted z B) (endpointRadius R N) B f
def inverseHeight (z R B d N : PTm n) : PTm n := GaussianBoundedInverseApartness.height gammaF P
  (baseGammaData z R B d N) (GaussianGammaBinomialCleared.baseData z R B N) (GaussianGammaC9Bound.majorant (baseRadius R N))
def inverseF : PR 2 := GaussianNameReciprocal.nameF gammaF
def inverseData (z R B d N : PTm n) : PTm n := GaussianNameReciprocal.nameData (inverseHeight z R B d N) (baseGammaData z R B d N)
def ratioF : PR 2 := multiplyF gammaF inverseF
def ratioData (z R B d f N : PTm n) : PTm n := multiplyData gammaF inverseF (topGammaData z R B f N) (inverseData z R B d N)
def nameF : PR 2 := multiplyF constantF ratioF
def data (z R B d f N : PTm n) : PTm n := multiplyData constantF ratioF (factorialInverse N) (ratioData z R B d f N)

theorem base_source (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (start z B N) (baseRadius R N) B a d :=
  .andI (GaussianGammaFallingFactorial.start_source z R B N h.andE₁) h.andE₂.andE₁
theorem top_source (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (shifted z B) (endpointRadius R N) B e f :=
  .andI (GaussianGammaFallingFactorial.endpoint_source z R B N h.andE₁) h.andE₂.andE₂

theorem majorant_positive (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx] le one (GaussianGammaC9Bound.majorant R) :=
  positive_product _ _ (positive_product _ _ hR (GaussianFactorBudget.power_positive _ _ (le_add_right one R)))
    (GaussianFactorBudget.power_positive _ _ (zero_lt_succ two))

/-- A finite anchor for the actual reciprocal of the original denominator
Gamma, derived from the actual C9-bounded inverse P at that endpoint. -/
theorem denominator_inverse (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.input gammaF (inverseHeight z R B d N) (baseGammaData z R B d N) ⋏
      crossEquivalent inverseF P (inverseData z R B d N) (GaussianGammaBinomialCleared.baseData z R B N) := by
  have hs := base_source z R B a d e f N h
  have hg := gamma_regular _ _ _ _ _ hs
  have hp := GaussianGammaBinomialCleared.base_regular z R B N h.andE₁
  have bounds : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples P
      (GaussianGammaBinomialCleared.baseData z R B N) (GaussianGammaC9Bound.majorant (baseRadius R N)) one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,GaussianRootApproximationWitness.pointBounds,GaussianGammaBinomialCleared.baseData,
      Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      GaussianGammaC9Bound.reciprocal_name_bound _ _ _ hs.andE₁
  have unitProduct := cross_trans _ _ _ _ _ _
    (GaussianNameRingLaws.multiply_commutative gammaF P (baseGammaData z R B d N) (GaussianGammaBinomialCleared.baseData z R B N) hg hp)
    (cross_trans _ _ _ _ _ _ (gamma_product _ _ _ _ _ hs)
      (GaussianBoundedInverseApartness.ones_equivalent (GaussianGammaBinomialCleared.baseData z R B N) (baseGammaData z R B d N)))
  exact GaussianBoundedInverseApartness.bounded_inverse_correct gammaF P _ _ _ one
    (majorant_positive _ hs.andE₁.andE₁) (le_refl one) hg hp bounds unitProduct

theorem inverse_regular (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    pointCN inverseF (inverseData z R B d N) :=
  GaussianNameReciprocal.name_fast _ _ _ (denominator_inverse z R B a d e f N h).andE₁.andE₁
    (denominator_inverse z R B a d e f N h).andE₁.andE₂
theorem ratio_regular (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    pointCN ratioF (ratioData z R B d f N) :=
  multiply_fast _ _ _ _ (gamma_regular _ _ _ _ _ (top_source z R B a d e f N h)) (inverse_regular z R B a d e f N h)
theorem name_regular (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B d f N) := multiply_fast _ _ _ _ (constant_regular _) (ratio_regular z R B a d e f N h)

theorem original_top_rising (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    crossEquivalent gammaF GaussianGammaRisingFactorial.risingF (topGammaData z R B f N)
      (GaussianGammaRisingFactorial.risingData (start z B N) (baseRadius R N) B d N) := by
  have hs := base_source z R B a d e f N h
  have ht := top_source z R B a d e f N h
  have same := GaussianRootAlgebra.equal_symm (GaussianGammaFallingFactorial.endpoint_native (Γ := Γ) z B N)
  have hp := GaussianGammaInputProperness.gamma_source_equal _ _ _ _ _ _ ht same
  have actualInput : Γ ⊢[PRAAx] GaussianGammaRisingFactorial.input (start z B N) (baseRadius R N) B a d e f N :=
    .andI hs hp.andE₂
  exact cross_trans _ _ _ _ _ _ (GaussianGammaInputProperness.original_Gamma_proper _ _ _ _ _ _ ht same)
    (GaussianGammaRisingFactorial.original_Gamma_rising_factorial _ _ _ _ _ _ _ _ actualInput)

/-- The quotient uses the actual named reciprocal of Gamma(z-N+1). -/
theorem original_ratio (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    crossEquivalent ratioF constantF (ratioData z R B d f N) (fallingProduct z B N) := by
  let F := fallingProduct z B N
  let G := baseGammaData z R B d N
  let T := topGammaData z R B f N
  let I := inverseData z R B d N
  have hf := constant_regular (Γ := Γ) F
  have hg := gamma_regular _ _ _ _ _ (base_source z R B a d e f N h)
  have ht := gamma_regular _ _ _ _ _ (top_source z R B a d e f N h)
  have hi := inverse_regular z R B a d e f N h
  have hc := GaussianGammaRisingFactorial.rising_regular (start z B N) (baseRadius R N) B a d N (base_source z R B a d e f N h)
  have replaced := GaussianGammaAdjacentCutoff.multiply_cross gammaF GaussianGammaRisingFactorial.risingF inverseF inverseF
    T (GaussianGammaRisingFactorial.risingData (start z B N) (baseRadius R N) B d N) I I ht hc hi hi
    (original_top_rising z R B a d e f N h) (cross_refl _ _ hi)
  have assoc := GaussianNameRingLaws.multiply_associative constantF gammaF inverseF F G I hf hg hi
  have sourceInverse := (denominator_inverse z R B a d e f N h).andE₁
  have unitProduct := cross_trans _ _ _ _ _ _
    (GaussianNameReciprocal.product_one gammaF (inverseHeight z R B d N) G sourceInverse.andE₁ sourceInverse.andE₂)
    (GaussianBoundedInverseApartness.ones_equivalent G F)
  have unitRegular := GaussianNameRingLaws.one_fast (Γ := Γ) F
  have canceled := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (multiplyF gammaF inverseF) oneF F F
    (multiplyData gammaF inverseF G I) F hf hf (multiply_fast _ _ _ _ hg hi) unitRegular
    (cross_refl _ _ hf) unitProduct
  exact cross_trans _ _ _ _ _ _ replaced (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ canceled (GaussianNameRingLaws.multiply_one constantF F hf)))

theorem original_Gamma_binomial_quotient (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    crossEquivalent nameF constantF (data z R B d f N) (binomial z B N) := by
  have hc := constant_regular (Γ := Γ) (factorialInverse N)
  have lifted := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF ratioF constantF
    (factorialInverse N) (factorialInverse N) (ratioData z R B d f N) (fallingProduct z B N)
    hc hc (ratio_regular z R B a d e f N h) (constant_regular _) (cross_refl _ _ hc) (original_ratio z R B a d e f N h)
  exact cross_trans _ _ _ _ _ _ lifted (GaussianGammaWeierstrassApproximant.constant_product_cross _ _)

theorem original_observations (p q z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B d f N)) (ap2 constantF q (binomial z B N))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_Gamma_binomial_quotient z R B a d e f N h)

theorem actual_original_Gamma_binomial_quotient_V9_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent nameF constantF (data (var 0) (var 1) (var 2) (var 4) (var 6) (var 7)) (binomial (var 0) (var 2) (var 7))) :=
  closeUniv 8 (.impI (original_Gamma_binomial_quotient _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Gamma_binomial_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 6) (var 8) (var 9)))
        (ap2 constantF (var 1) (binomial (var 2) (var 4) (var 9)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaBinomialQuotient
