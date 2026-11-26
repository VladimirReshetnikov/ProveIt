import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDilation
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerWeightedHalfDecay

/-!
# Actual quadratic grid cells and their Jacobian remainder

For u_i=(a*N+C*i)/(E*N), the map phi(u)=(c/d)*u^2 has
cell width 2(c/d)u_i*Delta u+(c/d)(Delta u)^2 exactly.
Both sides multiply the very same Gaussian row observation. Its supplied
norm M gives the genuine local Jacobian error, with no continuity or
change-of-variables conclusion assumed. Zero interval width is admitted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareCells

open_ipra
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qmul positive_product canonical_unique represents_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCompactRiemannName (grid)
open GaussianRationalQuadratureDilation (pullData)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (d E N : PTm n) : Fm PTm n := le one d ⋏ (le one E ⋏ le one N)
def nodeNumerator (i N a C : PTm n) : PTm n := a*N+C*i
def denominator (d E N : PTm n) : PTm n := d*(E*N)*(E*N)
def timeMap (c d t : PTm n) : PTm n := pairT (c*fstT t*fstT t) (d*sndT t*sndT t)
def node (i N c d a C E : PTm n) : PTm n :=
  fraction (c*nodeNumerator i N a C*nodeNumerator i N a C) (denominator d E N)
def cellWidth (i N c d a C E : PTm n) : PTm n :=
  fraction (c*C*(two*nodeNumerator i N a C+C)) (denominator d E N)
def linearWidth (i N c d a C E : PTm n) : PTm n :=
  fraction (two*c*C*nodeNumerator i N a C) (denominator d E N)
def remainder (N c d C E : PTm n) : PTm n := fraction (c*C*C) (denominator d E N)
def jacobian (c d t : PTm n) : PTm n := fraction (two*c*fstT t) (d*sndT t)

ipra_subst source
ipra_subst nodeNumerator
ipra_subst denominator
ipra_subst timeMap
ipra_subst node
ipra_subst cellWidth
ipra_subst linearWidth
ipra_subst remainder
ipra_subst jacobian

theorem denominator_positive (d E N : PTm n) (h : Γ ⊢[PRAAx] source d E N) : Γ ⊢[PRAAx]
    le one (denominator d E N) := positive_product _ _
      (positive_product _ _ h.andE₁ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂))
      (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂)

theorem fraction_add_same (A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (fraction A B) (fraction C B) ≐ fraction (A+C) B := by
  have rep := GaussianRationalHorner.qadd_represents (fraction A B) (fraction C B)
    (ComplexLogarithmRemainder.scale A ComplexLogarithmRemainder.oneCode)
    (ComplexLogarithmRemainder.scale C ComplexLogarithmRemainder.oneCode) B hB
    (GaussianRationalHorner.ofGaussian_represents _ B hB) (GaussianRationalHorner.ofGaussian_represents _ B hB)
  apply canonical_unique _ _ (ComplexLogarithmRemainder.scale (A+C) ComplexLogarithmRemainder.oneCode) B
    (GaussianRationalHorner.qadd_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ B hB) hB
    (hrv := GaussianRationalHorner.ofGaussian_represents _ B hB)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) rep
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
    GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps
  all_goals ring

theorem square_increment (c D A C : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qsub (fraction (c*(A+C)*(A+C)) D) (fraction (c*A*A) D) ≐ fraction (c*C*(two*A+C)) D := by
  have split : Γ ⊢[PRAAx] qadd (fraction (c*A*A) D) (fraction (c*C*(two*A+C)) D) ≐ fraction (c*(A+C)*(A+C)) D :=
    (fraction_add_same _ _ D hD).eqTrans (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _))
  exact (qsub_congr split.eqSymm (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hD))

theorem actual_cell_width (i N c d a C E : PTm n) (h : Γ ⊢[PRAAx] source d E N) : Γ ⊢[PRAAx]
    qsub (node (succ i) N c d a C E) (node i N c d a C E) ≐ cellWidth i N c d a C E := by
  have next : Γ ⊢[PRAAx] node (succ i) N c d a C E ≐
      fraction (c*(nodeNumerator i N a C+C)*(nodeNumerator i N a C+C)) (denominator d E N) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by unfold nodeNumerator; ipra_ring) (.eqRefl _)
  exact (qsub_congr next (.eqRefl _)).eqTrans
    (square_increment c (denominator d E N) (nodeNumerator i N a C) C (denominator_positive d E N h))

theorem cell_width_split (i N c d a C E : PTm n) (h : Γ ⊢[PRAAx] source d E N) : Γ ⊢[PRAAx]
    cellWidth i N c d a C E ≐ qadd (linearWidth i N c d a C E) (remainder N c d C E) :=
  ((fraction_add_same _ _ (denominator d E N) (denominator_positive d E N h)).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _))).eqSymm

theorem actual_linear_weight (i N c d a C E : PTm n) (h : Γ ⊢[PRAAx] source d E N) : Γ ⊢[PRAAx]
    qmul (GaussianRationalRiemannRefinement.weight C E N) (jacobian c d (grid i N a C E)) ≐ linearWidth i N c d a C E := by
  have en := positive_product E N h.andE₂.andE₁ h.andE₂.andE₂
  have den := positive_product d (E*N) h.andE₁ en
  have j : Γ ⊢[PRAAx] jacobian c d (grid i N a C E) ≐ fraction (two*c*nodeNumerator i N a C) (d*(E*N)) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul (.eqRefl _) (fst_pair _ _))
      (congrMul (.eqRefl _) (snd_pair _ _))
  exact (qmul_congr (.eqRefl _) j).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((GaussianRationalQuadratureDilation.weight_factor _ _ C E N den h.andE₂.andE₁ h.andE₂.andE₂).eqTrans
        (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by unfold nodeNumerator; ipra_ring) (by unfold denominator; ipra_ring))))

theorem local_jacobian_error (w M i N c d a C E : PTm n) (h : Γ ⊢[PRAAx] source d E N)
    (hw : Γ ⊢[PRAAx] bounded w M one) : Γ ⊢[PRAAx]
    distanceBounded (qmul (cellWidth i N c d a C E) w) (qmul (linearWidth i N c d a C E) w)
      (c*C*C*M) (denominator d E N) := by
  have hd := denominator_positive d E N h
  have diff : Γ ⊢[PRAAx] qsub (cellWidth i N c d a C E) (linearWidth i N c d a C E) ≐ remainder N c d C E :=
    (qsub_congr (cell_width_split i N c d a C E h) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hd))
  have rem : Γ ⊢[PRAAx] bounded (remainder N c d C E) (c*C*C) (denominator d E N) :=
    GaussianRationalReciprocal.bound_congr
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hd).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded _ _ hd)
  have close : Γ ⊢[PRAAx] distanceBounded (cellWidth i N c d a C E) (linearWidth i N c d a C E) (c*C*C) (denominator d E N) :=
    GaussianRationalReciprocal.bound_congr diff.eqSymm (.eqRefl _) (.eqRefl _) rem
  exact distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)
    (by ipra_ring) (.eqRefl _) (GaussianApproximateInverseDistance.multiply_distance w _ _ M _ _ hd hw close)

theorem actual_quadratic_grid_cell_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 3) (var 6) (var 1) ⟶ qsub
      (node (succ (var 0)) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
      (node (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐
      cellWidth (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (actual_cell_width _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_quadratic_cell_jacobian_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 5) (var 8) (var 3) ⟶ bounded (var 0) (var 1) one ⟶ distanceBounded
      (qmul (cellWidth (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 0))
      (qmul (linearWidth (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 0))
      (var 4*var 7*var 7*var 1) (denominator (var 5) (var 8) (var 3))) :=
  closeUniv 9 (.impI (.impI (local_jacobian_error _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareCells
