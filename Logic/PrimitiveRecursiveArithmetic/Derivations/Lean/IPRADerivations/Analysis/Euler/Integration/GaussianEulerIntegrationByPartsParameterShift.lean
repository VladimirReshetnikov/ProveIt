import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrationByPartsLinear
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadShift

/-!
# The original Euler integrand under the native parameter shift z+B

Only exponent algebra, the original positive rational logarithm's verified
exponential, and actual exponential addition are used. No Gamma recurrence
is used. The shifted original power name equals time times the old power
name, and the shifted original Euler name equals time times the old Euler
name. Every independently computed operation and exponential clock is
retained by named properness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsParameterShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerIntegrandName (coefficient logarithmF powerExponentF powerExponentData powerRadius powerF powerData
  nameF data source power_regular name_regular power_input)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qadd qmul ofGaussian represents canonical_unique represents_congr)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shifted_coefficient (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    coefficient (shifted z B) B ≐ qadd (coefficient z B) qone := by
  have rep := GaussianEulerIntegrandName.coefficient_represents (shifted z B) B hB
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (shifted z B) (ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode)) z := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [shifted,GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring
  have same : Γ ⊢[PRAAx] coefficient (shifted z B) B ≐ ofGaussian z B :=
    canonical_unique _ _ z B (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
      (represents_congr (.eqRefl _) native (.eqRefl _) rep) (GaussianRationalHorner.ofGaussian_represents z B hB)
  exact same.eqTrans ((GaussianEulerIntegrationByPartsLinear.coefficient_plus_one z B hB).eqSymm.eqTrans
    (GaussianRationalLinearProduct.qadd_commutative _ _))

private theorem add_cross (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hf' : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hg' : Γ ⊢[PRAAx] pointCN g' y')
    (he : Γ ⊢[PRAAx] crossEquivalent f f' x x') (he' : Γ ⊢[PRAAx] crossEquivalent g g' y y') : Γ ⊢[PRAAx]
    crossEquivalent (addF f g) (addF f' g') (addData x y) (addData x' y') :=
  GaussianNameArithmetic.add_equivalent _ _ _ _ _ _ _ _ hf hf' hg hg' (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ he')

private theorem constant_one (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF GaussianNameRingLaws.oneF (qone : PTm n) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (GaussianNameRingLaws.one_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianRationalSyntheticDivision.subst_qone,Syn.shift] using
    (constant_at (var 0) (qone : PTm (n+1))).eqTrans (GaussianNameRingLaws.one_at (var 0) (Syn.shift x)).eqSymm

theorem one_logarithm (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    crossEquivalent powerExponentF logarithmF
      (multiplyData constantF logarithmF qone (GaussianPositiveRationalLogarithm.data a b)) (GaussianPositiveRationalLogarithm.data a b) := by
  let y := GaussianPositiveRationalLogarithm.data a b
  have hl := GaussianPositiveRationalLogarithm.name_regular a b h
  have first := GaussianGammaAdjacentCutoff.multiply_cross constantF GaussianNameRingLaws.oneF logarithmF logarithmF qone y y y
    (constant_regular _) (GaussianNameRingLaws.one_fast _) hl hl (constant_one y) (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ first (GaussianNameRingLaws.multiply_one_left logarithmF y hl)

theorem power_exponent_shift (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent (addF powerExponentF logarithmF) powerExponentF
      (addData (powerExponentData z B a b) (GaussianPositiveRationalLogarithm.data a b)) (powerExponentData (shifted z B) B a b) := by
  let x := coefficient z B
  let c := coefficient (shifted z B) B
  let y := GaussianPositiveRationalLogarithm.data a b
  let oneData := multiplyData constantF logarithmF qone y
  have hx := constant_regular (Γ := Γ) x
  have hc := constant_regular (Γ := Γ) c
  have ho := constant_regular (Γ := Γ) (qone : PTm n)
  have hl := GaussianPositiveRationalLogarithm.name_regular a b h.andE₂
  have hp := GaussianEulerIntegrandName.power_exponent_regular z B a b h
  have hp1 := multiply_fast constantF logarithmF qone y ho hl
  have first := add_cross powerExponentF powerExponentF logarithmF powerExponentF
    (powerExponentData z B a b) (powerExponentData z B a b) y oneData hp hp hl hp1
    (cross_refl _ _ hp) (cross_symm _ _ _ _ (one_logarithm a b h.andE₂))
  have distribute := GaussianNameRingLaws.right_distributive constantF constantF logarithmF x qone y hx ho hl
  have coeff := cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross x qone)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (shifted_coefficient z B h.andE₁).eqSymm)
  have last := GaussianGammaAdjacentCutoff.multiply_cross (addF constantF constantF) constantF logarithmF logarithmF
    (addData x qone) c y y (add_fast _ _ _ _ hx ho) hc hl hl coeff (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ distribute) last)

def powerProductF : PR 2 := multiplyF constantF powerF
def powerProductData (z B a b : PTm n) : PTm n := multiplyData constantF powerF (fraction a b) (powerData z B a b)
def productF : PR 2 := multiplyF constantF nameF
def productData (z B a b : PTm n) : PTm n := multiplyData constantF nameF (fraction a b) (data z B a b)
@[simp] theorem subst_powerProductData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (powerProductData z B a b) = powerProductData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [powerProductData]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (productData z B a b) = productData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [productData]

theorem original_power_parameter_shift (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent powerF powerProductF (powerData (shifted z B) B a b) (powerProductData z B a b) := by
  have hs : Γ ⊢[PRAAx] source (shifted z B) B a b := h
  have hp := power_regular z B a b h
  have hl := GaussianPositiveRationalLogarithm.exponential_regular a b h.andE₂
  have law := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent powerExponentF logarithmF powerExponentF
    (powerRadius z B a b) (GaussianPositiveRationalLogarithm.radius a b) (powerRadius (shifted z B) B a b)
    (powerExponentData z B a b) (GaussianPositiveRationalLogarithm.data a b) (powerExponentData (shifted z B) B a b)
    (power_input z B a b h) (GaussianPositiveRationalLogarithm.exponential_input a b h.andE₂) (power_input (shifted z B) B a b hs)
    (power_exponent_shift z B a b h)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross powerF powerF GaussianPositiveRationalLogarithm.expF constantF
    (powerData z B a b) (powerData z B a b) (GaussianPositiveRationalLogarithm.expData a b) (fraction a b)
    hp hp hl (constant_regular _) (cross_refl _ _ hp) (GaussianPositiveRationalLogarithm.exponential_fraction a b h.andE₂)
  have commute := GaussianNameRingLaws.multiply_commutative powerF constantF (powerData z B a b) (fraction a b) hp (constant_regular _)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ law) (cross_trans _ _ _ _ _ _ replace commute)

theorem original_integrand_parameter_shift (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent nameF productF (data (shifted z B) B a b) (productData z B a b) := by
  let D := GaussianEulerIntegrandName.decayF
  let d := GaussianEulerIntegrandName.decayData a b
  let t := fraction a b
  let x := powerData z B a b
  let y := data z B a b
  have hs : Γ ⊢[PRAAx] source (shifted z B) B a b := h
  have hc := constant_regular (Γ := Γ) t
  have hp := power_regular z B a b h
  have hd := GaussianRadiusExponentialName.name_regular (Γ := Γ) constantF _ _
    (GaussianGammaFiniteApproximantName.exponential_input constantF (GaussianEulerIntegrandName.decayPoint a b) (constant_regular _))
  have old := GaussianEulerIntegrandName.original_power_times_decay z B a b h
  have first := GaussianGammaAdjacentCutoff.multiply_cross powerF powerProductF D D
    (powerData (shifted z B) B a b) (powerProductData z B a b) d d
    (power_regular (shifted z B) B a b hs) (multiply_fast constantF powerF t x hc hp) hd hd
    (original_power_parameter_shift z B a b h) (cross_refl _ _ hd)
  have assoc := GaussianNameRingLaws.multiply_associative constantF powerF D t x d hc hp hd
  have last := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (multiplyF powerF D) nameF
    t t (GaussianEulerIntegrandName.productData z B a b) y hc hc (multiply_fast powerF D x d hp hd) (name_regular z B a b h)
    (cross_refl _ _ hc) old
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianEulerIntegrandName.original_power_times_decay (shifted z B) B a b hs))
    (cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc last))

theorem original_power_parameter_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent powerF powerProductF
      (powerData (shifted (var 0) (var 1)) (var 1) (var 2) (var 3)) (powerProductData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_power_parameter_shift _ _ _ _ Prf.hyp0))
theorem original_Euler_integrand_parameter_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF productF
      (data (shifted (var 0) (var 1)) (var 1) (var 2) (var 3)) (productData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_integrand_parameter_shift _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsParameterShift
