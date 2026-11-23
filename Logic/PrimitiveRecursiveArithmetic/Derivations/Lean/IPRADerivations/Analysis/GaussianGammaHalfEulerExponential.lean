import IPRADerivations.Analysis.GaussianRobinMeshExponential

/-!
# Square of the original half-argument Euler exponential

The original numerical radius and both original exponential clocks are
retained. The named addition identity squares the original exponential,
and the harmonic-mesh reciprocal law identifies its square with (1/N).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfEulerExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (logF log_regular logExponentF logExponentData
  log_exponent_regular exponentialInputData exponential_input)
open GaussianGammaEulerShift (negativeLogData negative_log_regular constant_sum_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qadd qadd_represents canonical_unique represents_congr)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open GaussianRationalMatrixFiniteSums (minusOne)
open ComplexLogarithmRemainder (oneCode)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient : PTm n := qnegative (ofGaussian oneCode two)
def exponent (N : PTm n) : PTm n := logExponentData oneCode two N
def halfData (N : PTm n) : PTm n := exponentialInputData logExponentF (exponent N)
def expF : PR 2 := GaussianRadiusExponentialName.nameF logExponentF
def squareF : PR 2 := multiplyF expF expF
def squareData (N : PTm n) : PTm n := multiplyData expF expF (halfData N) (halfData N)

theorem coefficient_double : Γ ⊢[PRAAx] qadd (coefficient : PTm n) coefficient ≐ minusOne := by
  have hp : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one
  have h : Γ ⊢[PRAAx] GaussianRationalHorner.represents (coefficient : PTm n)
      (ComplexLogarithmRemainder.neg oneCode) two :=
    qnegative_represents _ _ _ (ofGaussian_represents _ _ hp)
  have lhs := qadd_represents _ _ _ _ _ hp h h
  have rhs := qnegative_represents _ _ _ (GaussianRationalReciprocal.qone_represents_scaled (Γ := Γ) two)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _) (qnegative_canonical _) hp ?_ rhs
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) lhs
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_neg,
      GaussianRootAlgebra.im_neg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> (ipra_simps; ring)

theorem exponent_double (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (addF logExponentF logExponentF) logExponentF
      (addData (exponent N) (exponent N)) (negativeLogData N) := by
  let c : PTm n := coefficient
  let m : PTm n := minusOne
  have hl : Γ ⊢[PRAAx] pointCN logF N := log_regular N hN
  have hc : Γ ⊢[PRAAx] pointCN constantF c := constant_regular c
  have hm : Γ ⊢[PRAAx] pointCN constantF m := constant_regular m
  have hconst : Γ ⊢[PRAAx] crossEquivalent (addF constantF constantF) constantF (addData c c) m :=
    cross_trans _ _ _ _ _ _ (constant_sum_cross c c)
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ coefficient_double)
  have dist := GaussianNameRingLaws.distributive logF constantF constantF N c c hl hc hc
  have fused := GaussianGammaAdjacentCutoff.multiply_cross logF logF (addF constantF constantF) constantF
    N N (addData c c) m hl hl (add_fast _ _ _ _ hc hc) hm (cross_refl logF N hl) hconst
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ dist) fused

theorem half_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN expF (halfData N) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (exponential_input _ _ (log_exponent_regular oneCode two N hN))

theorem square_value (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent squareF constantF (squareData N) (GaussianGammaEulerShiftLimit.reciprocalPoint N) := by
  let E := logExponentF
  let X := exponent N
  let Y := negativeLogData N
  let R := GaussianNameBounds.U E X
  let S := GaussianNameBounds.U E Y
  have ix : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input E R X :=
    exponential_input E X (log_exponent_regular oneCode two N hN)
  have iy : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input E S Y :=
    exponential_input E Y (negative_log_regular N hN)
  have squared := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent E E E R R S X X Y
    ix ix iy (exponent_double N hN)
  exact cross_trans _ _ _ _ _ _ squared (GaussianRobinMeshExponential.mesh_exponential_inverse N hN)

theorem original_half_Euler_exponent_double_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent (addF logExponentF logExponentF) logExponentF
      (addData (exponent (var 0)) (exponent (var 0))) (negativeLogData (var 0))) :=
  closeUniv 1 (.impI (exponent_double _ Prf.hyp0))

theorem original_half_Euler_exponential_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent squareF constantF (squareData (var 0))
      (GaussianGammaEulerShiftLimit.reciprocalPoint (var 0))) :=
  closeUniv 1 (.impI (square_value _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfEulerExponential
