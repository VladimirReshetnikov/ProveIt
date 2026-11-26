import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerShiftRate
import IPRADerivations.Analysis.Inequalities.GaussianRationalFactorialEulerSums

/-!
# Exact finite integration of an affine row remainder

The shifted, original, and linear row programs use the same grid but
can use different data. The interval weight commutes with the fixed
complex multiplier. The row error therefore integrates with exactly
the interval length, uniformly in the numerical number of rows.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureAffineRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalRiemannRefinement (leftSum weight termsDistance constantBody)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianEulerPowerShiftRate (displaced_difference)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBody (f g h : PTm 2) : PTm 2 := differenceBody (differenceBody f g) (multiplyBody h)
def rowData (c x y z : PTm n) : PTm n := pairT (pairT x y) (pairT c z)

@[simp] theorem subst_rowData {m : ℕ} (σ : Fin n → PTm m) (c x y z : PTm n) :
    Syn.subst σ (rowData c x y z) = rowData (Syn.subst σ c) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) := by
  simp [rowData]

theorem row_at (f g h : PTm 2) (i c x y z : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowBody f g h) i (rowData c x y z) ≐ qsub (inst2 f i x) (qadd (inst2 g i y) (qmul c (inst2 h i z))) :=
  (difference_body_at (differenceBody f g) (multiplyBody h) i (pairT x y) (pairT c z)).eqTrans
    ((qsub_congr (difference_body_at f g i x y) (multiply_body_at h c i z)).eqTrans
      (displaced_difference _ _ _ (GaussianRationalHorner.qmul_canonical _ _)))

private theorem left_sum_multiply (h : PTm 2) (c N z C E : PTm n) : Γ ⊢[PRAAx]
    leftSum (multiplyBody h) N (pairT c z) C E ≐ qmul c (leftSum h N z C E) := by
  let w := weight C E N
  exact (qmul_congr (.eqRefl w) (sum_multiply h c N z)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative w c (sum h N z)).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative w c) (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qmul_associative c w (sum h N z))))

theorem weighted_remainder (f g h : PTm 2) (c N x y z C E : PTm n) : Γ ⊢[PRAAx]
    leftSum (rowBody f g h) N (rowData c x y z) C E ≐
      qsub (leftSum f N x C E) (qadd (leftSum g N y C E) (qmul c (leftSum h N z C E))) :=
  (weighted_difference (differenceBody f g) (multiplyBody h) N (pairT x y) (pairT c z) C E).eqSymm.eqTrans
    ((qsub_congr (weighted_difference f g N x y C E).eqSymm (left_sum_multiply h c N z C E)).eqTrans
      (displaced_difference _ _ _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem weighted_bound (f g h : PTm 2) (c N x y z C E A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D)
    (rows : Γ ⊢[PRAAx] termsDistance (rowBody f g h) constantBody N (rowData c x y z) qzero A D) : Γ ⊢[PRAAx]
    distanceBounded (leftSum f N x C E) (qadd (leftSum g N y C E) (qmul c (leftSum h N z C E))) (C*A) (E*D) := by
  let r := sum (rowBody f g h) N (rowData c x y z)
  have zeros : Γ ⊢[PRAAx] sum constantBody N qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero N).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value N)
  have sumBound : Γ ⊢[PRAAx] bounded r (N*A) D := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMp
    (GaussianRationalDistanceOrder.distance_congr (.eqRefl _) zeros (.eqRefl _) (.eqRefl _)
      (GaussianRationalRiemannRefinement.sum_distance _ _ _ _ _ _ _ hD rows))
  have weightDen : Γ ⊢[PRAAx] le one (E*N) := positive_product _ _ hE hN
  have scaled := bounded_product _ _ _ _ _ _ weightDen hD
    (GaussianRationalRiemannRefinement.weight_bound C E N hE hN) sumBound
  have simplified := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ (C*A) (E*D)
    (positive_product _ _ weightDen hD) (positive_product _ _ hE hD)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) scaled
  exact bound_congr (weighted_remainder f g h c N x y z C E) (.eqRefl _) (.eqRefl _) simplified

theorem actual_finite_quadrature_affine_remainder_closed (f g h : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((le one (var 1) ⋏ (le one (var 6) ⋏ le one (var 8))) ⋏
      termsDistance (rowBody f g h) constantBody (var 1) (rowData (var 0) (var 2) (var 3) (var 4)) qzero (var 7) (var 8) ⟶
        distanceBounded (leftSum f (var 1) (var 2) (var 5) (var 6))
          (qadd (leftSum g (var 1) (var 3) (var 5) (var 6)) (qmul (var 0) (leftSum h (var 1) (var 4) (var 5) (var 6))))
          (var 5*var 7) (var 6*var 8)) :=
  closeUniv 9 (.impI (weighted_bound f g h _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁
    Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureAffineRemainder
