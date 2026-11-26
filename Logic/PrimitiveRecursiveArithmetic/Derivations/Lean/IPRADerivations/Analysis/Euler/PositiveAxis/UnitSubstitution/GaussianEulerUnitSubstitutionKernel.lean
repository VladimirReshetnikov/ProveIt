import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitLogarithmicComposition
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName

/-!
# Actual pointwise kernel for the unit-interval Euler substitution

At a positive rational u=a/b<1 the inner time is the actual positive
harmonic log(b/a). The actual outer logarithm and original complex
exponential evaluate exp((z/B-1)*log(time)). Both nested logarithm
queries, the multiplication query and the original finite exponential
cutoff are retained. Pointwise regularity uses only the numerical source;
a uniform interval modulus and change of variables are separate results.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionKernel

open_ipra
open GaussianEulerIntegrandName (coefficient)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := GaussianEulerUnitLogarithmicComposition.nameF
def source (_z B a b : PTm n) : Fm PTm n := le one B ⋏ GaussianEulerUnitLogarithmicMargin.source a b
abbrev exponentF : PR 2 := multiplyF constantF logarithmF
def exponentData (z B a b : PTm n) : PTm n := multiplyData constantF logarithmF
  (coefficient z B) (GaussianEulerUnitLogarithmicComposition.data a b)
def radius (z B a b : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData z B a b)
abbrev nameF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def data (z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius z B a b) (exponentData z B a b)
def powerClock (p z B a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (multiplyModulus constantF logarithmF (coefficient z B) (GaussianEulerUnitLogarithmicComposition.data a b)) p
def exponentClock (p z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.inputPrecision (radius z B a b) p
def cutoff (p z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.index (radius z B a b) p

ipra_subst source
ipra_subst exponentData
ipra_subst radius
ipra_subst data
ipra_subst powerClock
ipra_subst exponentClock
ipra_subst cutoff

theorem exponent_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    pointCN exponentF (exponentData z B a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianEulerUnitLogarithmicComposition.name_regular a b h.andE₂)

theorem exponential_input (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (radius z B a b) (exponentData z B a b) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _ (exponent_regular z B a b h)

theorem name_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    pointCN nameF (data z B a b) := GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input z B a b h)

theorem exponent_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 exponentF p (exponentData z B a b) ≐ qmul (coefficient z B)
      (GaussianEulerUnitLogarithmicComposition.sample (powerClock p z B a b) a b) :=
  (GaussianNameArithmetic.multiply_at constantF logarithmF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem original_finite_sample (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z B a b) ≐ GaussianRationalPolynomialExponential.scalarSum
      (qmul (coefficient z B) (GaussianEulerUnitLogarithmicComposition.observation
        (powerClock (exponentClock p z B a b) z B a b) a b)) (cutoff p z B a b) :=
  (GaussianRadiusExponentialName.sample_at exponentF (radius z B a b) p (exponentData z B a b)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      ((exponent_at (exponentClock p z B a b) z B a b).eqTrans
        (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianEulerUnitLogarithmicComposition.sample_at _ a b))))

theorem original_observations (p q z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z B a b)) (ap2 nameF q (data z B a b)) (unit p+unit q) (unit p*unit q) :=
  GaussianNameEquivalence.point_at _ _ p q (name_regular z B a b h)

theorem actual_unit_substitution_pointwise_kernel_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))

theorem actual_unit_substitution_literal_kernel_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) ≐ GaussianRationalPolynomialExponential.scalarSum
      (qmul (coefficient (var 1) (var 2)) (GaussianEulerUnitLogarithmicComposition.observation
        (powerClock (exponentClock (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2) (var 3) (var 4)) (var 3) (var 4)))
      (cutoff (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (original_finite_sample _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionKernel
