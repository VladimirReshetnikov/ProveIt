import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.FiniteHeads.GaussianLogGammaEulerNormalizedHead
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.ResidualBounds.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperPowerCancellation

/-!
# Match the canonical numerator exponent with the original Euler power

The negative of the actual canonical numerator logarithm z log(N) is
the original mesh exponent used by the reciprocal Euler approximant.
Both normalized arithmetic programs retain their independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialNumerator

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (logExponentF logExponentData log_exponent_regular exponentialInputData exponential_input)
open GaussianLogGammaEulerHead (argument productF productData)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_to_diagonal)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_sample_error negative_equivalent multiply_sample_error three)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalMetric (qnegative qnegative_canonical qsub distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF

private def signBudget (f : PR 2) (x z : PTm n) : PTm n :=
  three+(multiplyModulus f constantF x z+one)+(multiplyModulus f constantF x (qnegative z)+one)

private theorem sign_at (f : PR 2) (p x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (negativeF (multiplyF f constantF)) p (negativeData (multiplyData f constantF x z)))
      (ap2 (multiplyF f constantF) p (multiplyData f constantF x (qnegative z)))
      (signBudget f x z) (unit p) := by
  let g := multiplyF f constantF
  let y := multiplyData f constantF x z
  let a := ap2 g p y
  let w := ap2 f p x
  let v := qmul w z
  have hp := unit_positive (Γ := Γ) p
  have hg := multiply_fast f constantF x z hf (constant_regular z)
  have sign := distance_congr (.eqRefl _) (qzero_add _ (qnegative_canonical a))
    (.eqRefl _) (.eqRefl _) (negative_sample_error g y p hg)
  have left := distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p z))
    (.eqRefl _) (.eqRefl _) (multiply_sample_error f constantF x z p hf (constant_regular z))
  have negated := GaussianNamedDifference.negative_distance a v _ _ hp left
  have base : Γ ⊢[PRAAx] qnegative v ≐ qmul w (qnegative z) :=
    (GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative w z)).eqTrans
      ((GaussianInverseBinomialRows.negative_product z w).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  have right := distance_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (constant_at p (qnegative z))).eqTrans base.eqSymm)
    (.eqRefl _) (.eqRefl _) (multiply_sample_error f constantF x (qnegative z) p hf (constant_regular (qnegative z)))
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp sign negated)
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hp right)

private theorem negate_weighted_name (f : PR 2) (x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF (multiplyF f constantF)) (multiplyF f constantF)
      (negativeData (multiplyData f constantF x z)) (multiplyData f constantF x (qnegative z)) := by
  have left := negative_fast _ _ (multiply_fast f constantF x z hf (constant_regular z))
  have right := multiply_fast f constantF x (qnegative z) hf (constant_regular (qnegative z))
  refine cross_of_diagonal_rate _ _ _ _ (signBudget f x z) left right (.allI ?_)
  have h : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hf.shift
  simpa [diagonalRate,signBudget,Syn.shift,three,one] using
    sign_at f (var 0) (Syn.shift x) (Syn.shift z) h

theorem negative_exponent (A B D neg N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF productF) logExponentF
      (negativeData (productData A B D neg N)) (logExponentData (native A B neg) D N) := by
  let z := argument A B D neg
  let f := GaussianPositiveRationalLogarithm.logF
  let g := GaussianGammaFiniteApproximantName.logF
  let x := GaussianPositiveRationalLogarithm.data N one
  let y := multiplyData constantF g z N
  let w := multiplyData g constantF N z
  have hC := constant_regular (Γ := Γ) z
  have hf := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have hg := GaussianGammaFiniteApproximantName.log_regular N hN
  have replace := multiply_cross constantF constantF f g z z x N hC hC hf hg
    (cross_refl _ _ hC) (GaussianBetaUpperPowerCancellation.rational_log_integer N hN)
  have swap := GaussianNameRingLaws.multiply_commutative constantF g z N hC hg
  have old := GaussianLogGammaEulerNormalizedHead.product_regular A B D neg N hN
  have cur := multiply_fast g constantF N z hg hC
  have negated := negative_equivalent productF (multiplyF g constantF) (productData A B D neg N) w old cur
    (cross_to_diagonal _ _ _ _ (cross_trans productF (multiplyF constantF g) (multiplyF g constantF) _ y w replace swap))
  exact cross_trans _ _ _ _ _ _ negated (negate_weighted_name g N z hg)

theorem negative_exponential (A B D neg N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (E (negativeF productF)) (E logExponentF)
      (exponentialInputData (negativeF productF) (negativeData (productData A B D neg N)))
      (exponentialInputData logExponentF (logExponentData (native A B neg) D N)) := by
  have hl := negative_fast _ _ (GaussianLogGammaEulerNormalizedHead.product_regular A B D neg N hN)
  have hr := log_exponent_regular (native A B neg) D N hN
  exact GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (exponential_input _ _ hl) (exponential_input _ _ hr) (negative_exponent A B D neg N hN)

theorem original_Euler_mesh_exponent_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 4) ⟶ crossEquivalent (E (negativeF productF)) (E logExponentF)
        (exponentialInputData (negativeF productF) (negativeData (productData (var 0) (var 1) (var 2) (var 3) (var 4))))
        (exponentialInputData logExponentF (logExponentData (native (var 0) (var 1) (var 3)) (var 2) (var 4)))) :=
  closeUniv 5 (.impI (negative_exponential _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialNumerator
