import IPRADerivations.Analysis.Gamma.GaussianGammaHalfEulerHead
import IPRADerivations.Analysis.Gamma.GaussianGammaHalfEulerExponential
import IPRADerivations.Analysis.Stirling.GaussianGammaHalfWallisRate

/-!
# Exact square of the original finite Gamma at one half

The original pole-free reciprocal name of the finite Euler approximant has
the square (4N(2N)!!^2/(2N+1)!!^2). The existing named inverse law and the
exact head and exponential values derive this identity. In particular the
finite expression agrees with the same double-factorial Wallis expression
that is compared with the arctangent quadrature.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfEulerSquare

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfEulerHead (numerator denominator value original_run numerator_positive denominator_positive)
open GaussianGammaHalfWallisRate (squareNum squareDen wallisValue square_denominator square_denominator_positive)
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData euler_regular euler_product)
open GaussianGammaReciprocalInverse (named_product_exchange inverse_pairs constant_inverse)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one multiply_one_left)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian positive_product qmul)
open GaussianRationalSyntheticDivision (qone)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianCompactRiemannName (fraction_congr)
open ComplexLogarithmRemainder (oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def squareF (f : PR 2) : PR 2 := multiplyF f f
def squareData (f : PR 2) (x : PTm n) : PTm n := multiplyData f f x x
def qHalf (N : PTm n) : PTm n := qData oneCode two N
def eulerHalf (N : PTm n) : PTm n := eulerData oneCode one two two N
def reciprocalSquare (N : PTm n) : PTm n := fraction (squareDen N) (squareNum N)

@[simp] theorem subst_squareData {k : ℕ} (σ : Fin n → PTm k) (f : PR 2) (x : PTm n) :
    Syn.subst σ (squareData f x) = squareData f (Syn.subst σ x) := by simp [squareData]

theorem euler_source (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source oneCode one two one two N :=
  .andI (GaussianGammaDensityDomain.base_gamma_source oneCode one two two GaussianGammaHalfIntegerDomain.half_source)
    (le_congr (.eqRefl _) (.eqRefl _) (le_congr (by ipra_ring : Γ ⊢[PRAAx] two ≐ two*one) (.eqRefl _) hN))

theorem square_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (squareNum N) := by
  have he : Γ ⊢[PRAAx] le one (WallisFinite.db N) :=
    le_congr (.eqRefl _) (LeanProofs.IPRA.Probability.NormalMoments.edf_eq (Γ := Γ) N).eqSymm
      (positive_product _ _ (GaussianCoefficientNameBounds.unit_positive N) (GaussianGammaHalfRisingFactorial.factorial_positive N))
  have four : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by
    exact zero_lt_succ _
  exact positive_product _ _ (positive_product _ _ four hN) (positive_product _ _ he he)

theorem inverse_fraction (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (fraction a b) (fraction b a) ≐ qone := by
  have d := positive_product _ _ ha hb
  have shuffle : Γ ⊢[PRAAx] fraction (a*b) (b*a) ≐ fraction ((a*b)*one) ((a*b)*one) :=
    fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
  exact (fraction_product a b b a hb ha).eqTrans (shuffle.eqTrans
    ((GaussianCompactRiemannSplit.fraction_cancel (a*b) one one d (le_refl one)).eqTrans GaussianGammaFactorialValues.natural_one))

theorem reciprocal_fraction (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianGammaEulerShiftLimit.reciprocalPoint N ≐ fraction one N := by
  apply GaussianGammaFiniteValueProperness.fraction_equal _ _ N hN
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> (ipra_simps; ring)

theorem q_square_value (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (squareF qF) constantF (squareData qF (qHalf N)) (reciprocalSquare N) := by
  let E := GaussianGammaHalfEulerExponential.expF
  let e := GaussianGammaHalfEulerExponential.halfData N
  let X := GaussianGammaEulerHead.run oneCode two N
  let S := squareF constantF
  let H := numerator N
  let D := denominator N
  let C := qmul (value N) (value N)
  let t := GaussianGammaEulerShiftLimit.reciprocalPoint N
  have hx : Γ ⊢[PRAAx] pointCN constantF X := constant_regular _
  have he : Γ ⊢[PRAAx] pointCN E e := GaussianGammaHalfEulerExponential.half_regular N hN
  have ex := named_product_exchange constantF E constantF E X e X e hx he hx he
  have firstHead := constant_product_cross (Γ := Γ) X X
  have pointHead : Γ ⊢[PRAAx] qmul X X ≐ C :=
    GaussianRationalSyntheticDivision.qmul_congr (original_run N) (original_run N)
  have head := cross_trans _ _ _ _ _ _ firstHead (constant_data_cross _ _ pointHead)
  have exponential := GaussianGammaHalfEulerExponential.square_value N hN
  have combined := multiply_cross S constantF (squareF E) constantF (squareData constantF X) C (squareData E e) t
    (multiply_fast _ _ _ _ hx hx) (constant_regular _) (multiply_fast _ _ _ _ he he) (constant_regular _) head exponential
  have hD : Γ ⊢[PRAAx] le one D := denominator_positive N
  have eq : Γ ⊢[PRAAx] qmul C t ≐ reciprocalSquare N := by
    have prod := GaussianRationalSyntheticDivision.qmul_congr
      (fraction_product H D H D hD hD) (reciprocal_fraction N hN)
    exact prod.eqTrans ((fraction_product (H*H) (D*D) one N (positive_product _ _ hD hD) hN).eqTrans
      (fraction_congr _ _ _ _ ((by ipra_ring : Γ ⊢[PRAAx] H*H*one ≐ H*H).eqTrans (square_denominator N).eqSymm)
        (by unfold D denominator squareNum GaussianGammaHalfWallisRate.evenSquare; ipra_ring)))
  exact cross_trans _ _ _ _ _ _ ex (cross_trans _ _ _ _ _ _ combined
    (cross_trans _ _ _ _ _ _ (constant_product_cross C t) (constant_data_cross _ _ eq)))

private theorem cancel_inverse_constant (F : PR 2) (x a b : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hab : Γ ⊢[PRAAx] qmul a b ≐ qone)
    (h : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF F) oneF
      (multiplyData constantF F b x) a) :
    Γ ⊢[PRAAx] crossEquivalent F constantF x a := by
  let C := constantF
  let C2 := multiplyF C C
  let Y := multiplyData C C a b
  let BX := multiplyData C F b x
  have ha : Γ ⊢[PRAAx] pointCN C a := constant_regular _
  have hb : Γ ⊢[PRAAx] pointCN C b := constant_regular _
  have liftAtOne := multiply_cross C2 oneF F F Y x x x (multiply_fast _ _ _ _ ha hb) (one_fast x)
    hx hx (constant_inverse a b x hab) (cross_refl F x hx)
  have left := cross_trans _ _ _ _ _ _ liftAtOne (multiply_one_left F x hx)
  have assoc := multiply_associative C C F a b x ha hb hx
  have lift := multiply_cross C C (multiplyF C F) oneF a a BX a ha ha
    (multiply_fast _ _ _ _ hb hx) (one_fast a) (cross_refl C a ha) h
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ lift (multiply_one C a ha)))

theorem euler_square_value (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] crossEquivalent (squareF eulerF) constantF (squareData eulerF (eulerHalf N)) (wallisValue N) := by
  let X := qHalf N
  let Y := eulerHalf N
  let c := wallisValue N
  let r := reciprocalSquare N
  have src := euler_source N hN
  have hp : Γ ⊢[PRAAx] le one N := le_trans (zero_lt_succ one) hN
  have hq : Γ ⊢[PRAAx] pointCN qF X := q_regular oneCode two N hp
  have he : Γ ⊢[PRAAx] pointCN eulerF Y := euler_regular oneCode one two one two N src
  have p : Γ ⊢[PRAAx] crossEquivalent (multiplyF qF eulerF) oneF (multiplyData qF eulerF X Y) c :=
    cross_trans _ _ _ _ _ _ (euler_product oneCode one two one two N src)
      (GaussianBoundedInverseApartness.ones_equivalent X c)
  have unit := inverse_pairs qF qF eulerF eulerF X X Y Y c hq hq he he p p
  have hsq : Γ ⊢[PRAAx] pointCN (squareF eulerF) (squareData eulerF Y) :=
    multiply_fast _ _ _ _ he he
  have lift := multiply_cross constantF (squareF qF) (squareF eulerF) (squareF eulerF)
    r (squareData qF X) (squareData eulerF Y) (squareData eulerF Y) (constant_regular _)
    (multiply_fast _ _ _ _ hq hq) hsq hsq (cross_symm _ _ _ _ (q_square_value N hp)) (cross_refl _ _ hsq)
  exact cancel_inverse_constant _ _ c r hsq (inverse_fraction _ _ (square_positive N hp) (square_denominator_positive N))
    (cross_trans _ _ _ _ _ _ lift unit)

theorem actual_half_Q_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent (squareF qF) constantF (squareData qF (qHalf (var 0))) (reciprocalSquare (var 0))) :=
  closeUniv 1 (.impI (q_square_value _ Prf.hyp0))

theorem actual_half_Euler_Gamma_square_Wallis_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ crossEquivalent (squareF eulerF) constantF (squareData eulerF (eulerHalf (var 0))) (wallisValue (var 0))) :=
  closeUniv 1 (.impI (euler_square_value _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfEulerSquare
