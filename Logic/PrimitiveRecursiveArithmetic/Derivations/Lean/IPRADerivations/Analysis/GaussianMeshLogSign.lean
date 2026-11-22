import IPRADerivations.Analysis.GaussianGammaEulerShiftLimit
import IPRADerivations.Analysis.GaussianExponentialInverse
import IPRADerivations.Analysis.GaussianRationalNaturalScale

/-!
# The sign of the original mesh exponential

Multiplication of the mesh logarithm by the original negative unit and
the independent named negation have the same raw rational values.
The checked exponential inverse therefore turns a positive exponential
identity into the exact negative identity used by the Euler shift.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMeshLogSign

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (logF logExponentF log_regular exponentialInputData exponential_input)
open GaussianGammaEulerShift (expF negativeLogData negativeLogExpData negative_log_regular negative_log_exp_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyRawF multiplyModulus)
open GaussianNameRingLaws (negativeF negativeData negativeRawF oneF one_fast one_at)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalMetric (qnegative qsub distanceBounded)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents qzero qmul qmul_represents qmul_canonical canonical_unique represents_congr)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_add)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveF : PR 2 := GaussianRadiusExponentialName.nameF logF
def positiveData (N : PTm n) : PTm n := exponentialInputData logF N
def positiveIdentity (N : PTm n) : Fm PTm n :=
  crossEquivalent positiveF constantF (positiveData N) (naturalPoint N)
def inversePoint (N : PTm n) : PTm n := ofGaussian oneCode N

theorem negation_raw (p N : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyRawF logF constantF) p (GaussianNameArithmetic.data N minusOne) ≐
      ap2 (negativeRawF logF) p N := by
  let q := ap2 logF p N
  have first := GaussianNameArithmetic.multiply_raw_at (Γ := Γ) logF constantF p N (minusOne : PTm n)
  have swap := GaussianRationalPowerAlgebra.qmul_commutative (Γ := Γ) q (minusOne : PTm n)
  have last : Γ ⊢[PRAAx] qsub qzero q ≐ qnegative q :=
    qzero_add _ (GaussianRationalMetric.qnegative_canonical q)
  exact first.eqTrans ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (constant_at p minusOne)).eqTrans
    (swap.eqTrans ((negative_as_minusOne q).eqSymm.eqTrans
      (last.eqSymm.eqTrans (GaussianNameRingLaws.negative_raw_at logF N p).eqSymm))))

theorem original_log_negation (N : PTm n) (h : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent logExponentF (negativeF logF) (negativeLogData N) (negativeData N) := by
  have hf := log_regular N h
  refine GaussianValueNormalizerExtensionality.normalized_names_equivalent
    (multiplyRawF logF constantF) (negativeRawF logF)
    (multiplyModulus logF constantF N minusOne) (one+one) (GaussianNameArithmetic.data N minusOne) N zero
    (GaussianNameArithmetic.multiply_regular _ _ _ _ hf (constant_regular minusOne))
    (GaussianNameRingLaws.negative_regular logF N hf) (.allI ?_)
  let C := Γ.map Fm.shift
  let m := Syn.shift N
  let p : PTm (n+1) := var 0
  have e := negation_raw (Γ := C) p m
  have metric := GaussianRationalPowerDifference.distance_refl_zero (Γ := C)
    (ap2 (negativeRawF logF) p m) (unit p) (unit_positive p)
  simpa only [Syn.shift,GaussianNameArithmetic.subst_data,GaussianRationalMatrixFiniteSums.subst_minusOne,
    ConciseIPRA.PTm.subst_zero,C,m,p] using
    distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) metric

theorem inverse_point_product (N : PTm n) (h : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (inversePoint N) (naturalPoint N) ≐ qone := by
  let D := N*one
  have hd : Γ ⊢[PRAAx] le one D := le_congr (.eqRefl _) (by unfold D; ipra_ring) h
  have r := qmul_represents (inversePoint N) (naturalPoint N) oneCode (scale N oneCode) N one h (le_refl _)
    (ofGaussian_represents oneCode N h) (natural_point_represents N)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.mul oneCode (scale N oneCode)) (scale D oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,D] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ D (qmul_canonical _ _) qone_canonical hd
    (represents_congr (.eqRefl _) same (.eqRefl _) r) (GaussianRationalReciprocal.qone_represents_scaled D)

private theorem one_at_either_data (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF oneF x y := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let X := Syn.shift (Syn.shift x)
  let Y := Syn.shift (Syn.shift y)
  have hx := one_at (Γ := C) (var 0) X
  have hy := one_at (Γ := C) (var 0) Y
  exact distance_congr (.eqRefl _) (hx.eqTrans hy.eqSymm) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.point_at oneF X (var 1) (var 0) (one_fast X))

theorem cancel_constant (g : PR 2) (x y d : PTm n) (hg : Γ ⊢[PRAAx] pointCN g d)
    (hInv : Γ ⊢[PRAAx] qmul y x ≐ qone)
    (hProd : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF g) oneF (multiplyData constantF g x d) x) :
    Γ ⊢[PRAAx] crossEquivalent g constantF d y := by
  let F := constantF
  let M := multiplyF F F
  let m := multiplyData F F y x
  let G := multiplyF F g
  let v := multiplyData F g x d
  have hx : Γ ⊢[PRAAx] pointCN F x := constant_regular x
  have hy : Γ ⊢[PRAAx] pointCN F y := constant_regular y
  have ho := one_fast (Γ := Γ) d
  have e := GaussianGammaReciprocalInverse.constant_inverse y x d hInv
  have a := GaussianGammaAdjacentCutoff.multiply_cross oneF M g g d m d d ho
    (multiply_fast F F y x hy hx) hg hg (cross_symm _ _ _ _ e) (cross_refl _ _ hg)
  have b := GaussianNameRingLaws.multiply_associative F F g y x d hy hx hg
  have c := GaussianGammaAdjacentCutoff.multiply_cross F F G oneF y y v y hy hy
    (multiply_fast F g x d hx hg) (one_fast y) (cross_refl _ _ hy)
    (cross_trans _ _ _ _ _ _ hProd (one_at_either_data x y))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_one_left g d hg))
    (cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b
      (cross_trans _ _ _ _ _ _ c (GaussianNameRingLaws.multiply_one F y hy))))

theorem negative_mesh_reciprocal (N : PTm n) (h : Γ ⊢[PRAAx] le one N)
    (hPositive : Γ ⊢[PRAAx] positiveIdentity N) :
    Γ ⊢[PRAAx] GaussianGammaEulerShiftLimit.logInverse N := by
  let R := GaussianNameBounds.U logF N
  let W := GaussianNameBounds.U logExponentF (negativeLogData N)
  let F := positiveF
  let X := positiveData N
  let G := expF
  let Y := negativeLogExpData N
  let H := GaussianRadiusExponentialName.nameF (negativeF logF)
  let Z := GaussianRadiusExponentialName.data R (negativeData N)
  let nPoint := naturalPoint N
  have ip := exponential_input _ _ (log_regular N h)
  have im := exponential_input _ _ (negative_log_regular N h)
  have ineg := GaussianExponentialInverse.negative_input logF R N ip
  have hp : Γ ⊢[PRAAx] pointCN F X := GaussianRadiusExponentialName.name_regular _ _ _ ip
  have hm : Γ ⊢[PRAAx] pointCN G Y := negative_log_exp_regular N h
  have hn : Γ ⊢[PRAAx] pointCN H Z := GaussianRadiusExponentialName.name_regular _ _ _ ineg
  have cross := GaussianExponentialRadiusIndependence.independent_radii_proper
    logExponentF (negativeF logF) W R (negativeLogData N) (negativeData N) im ineg (original_log_negation N h)
  have act := GaussianGammaAdjacentCutoff.multiply_cross constantF F G H nPoint X Y Z
    (constant_regular _) hp hm hn (cross_symm _ _ _ _ hPositive) cross
  have pair := GaussianExponentialInverse.exponential_inverse logF R N ip
  have result := cross_trans _ _ _ _ _ _ act (cross_trans _ _ _ _ _ _ pair (one_at_either_data N nPoint))
  exact cancel_constant G nPoint (inversePoint N) Y hm (inverse_point_product N h) result

theorem original_mesh_sign_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ positiveIdentity (var 0) ⟶ GaussianGammaEulerShiftLimit.logInverse (var 0)) :=
  closeUniv 1 (.impI (.impI (negative_mesh_reciprocal _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianMeshLogSign
