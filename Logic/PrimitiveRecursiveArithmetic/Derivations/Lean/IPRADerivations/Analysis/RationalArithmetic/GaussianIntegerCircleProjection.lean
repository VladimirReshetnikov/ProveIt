import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalCircleParametrization
import IPRADerivations.Analysis.Geometry.GaussianRelativeNormTriangle

/-!
# Exact integer errors of the actual rational circle projection

The denominator and signed numerator are computed by the checked circle
program. A nonnegative disk deficit gives an exact integer cross-error
identity. Every coordinate, denominator, sign bit and deficit is numerical.
No unit-output or distance-output property is an incoming hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianIntegerCircleProjection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (code re im normSq normSq_eval scale)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (sub re_sub im_sub re_scale im_scale)
open LeanProofs.IPRA.Analysis.GaussianRationalCircleParametrization (bit)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def sign (b : PTm n) : ZT n := ZT.ofNat one-ZT.ofNat (two*b)
def plane (x V b : PTm n) : PTm n := code (ZT.ofNat x) (sign b*ZT.ofNat V)
def circleDen (x V S : PTm n) : PTm n := GaussianRationalCircleParametrization.denominator (S+x) V
def circleNum (x V b S : PTm n) : PTm n := GaussianRationalCircleParametrization.numerator (S+x) V b
def cross (x V b S : PTm n) : PTm n := sub (scale S (circleNum x V b S)) (scale (circleDen x V S) (plane x V b))

@[simp] theorem subst_sign {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) :
    (sign b).subst σ = sign (Syn.subst σ b) := by simp [sign]
@[simp] theorem subst_plane {m : ℕ} (σ : Fin n → PTm m) (x V b : PTm n) :
    Syn.subst σ (plane x V b) = plane (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ b) := by simp [plane]
@[simp] theorem subst_circleDen {m : ℕ} (σ : Fin n → PTm m) (x V S : PTm n) :
    Syn.subst σ (circleDen x V S) = circleDen (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ S) := by simp [circleDen]
@[simp] theorem subst_circleNum {m : ℕ} (σ : Fin n → PTm m) (x V b S : PTm n) :
    Syn.subst σ (circleNum x V b S) = circleNum (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ b) (Syn.subst σ S) := by simp [circleNum]
@[simp] theorem subst_cross {m : ℕ} (σ : Fin n → PTm m) (x V b S : PTm n) :
    Syn.subst σ (cross x V b S) = cross (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ b) (Syn.subst σ S) := by simp [cross]

theorem re_plane (x V b : PTm n) : ZT.toZ Γ (re (plane x V b)) = 𝔞(x) := by
  rw [plane,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat]

theorem im_plane (x V b : PTm n) : ZT.toZ Γ (im (plane x V b)) = ZT.toZ Γ (sign b)*𝔞(V) := by
  rw [plane,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_mul,ZT.toZ_ofNat]

theorem plane_norm (x V b : PTm n) (hb : Γ ⊢[PRAAx] bit b) : Γ ⊢[PRAAx]
    normSq (plane x V b) ≐ x*x+V*V := by
  refine .orE hb ?_ ?_
  · have e := natEq (Prf.hyp0 : (b ≐ zero)::Γ ⊢[PRAAx] b ≐ zero)
    apply deriveNat
    rw [normSq_eval,re_plane,im_plane]
    simp only [sign,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    rw [e]
    ring
  · have e := natEq (Prf.hyp0 : (b ≐ one)::Γ ⊢[PRAAx] b ≐ one)
    apply deriveNat
    rw [normSq_eval,re_plane,im_plane]
    simp only [sign,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    rw [e]
    ring

theorem cross_re (x V b S e : PTm n) (hGap : Γ ⊢[PRAAx] S*S ≐ x*x+V*V+e) :
    ZT.toZ Γ (re (cross x V b S)) = 𝔞((S+x)*e) := by
  have gap := natEq hGap
  simp only [cross,re_sub,re_scale,circleNum,GaussianRationalCircleParametrization.re_numerator,
    GaussianRationalCircleParametrization.realNumerator,ZT.toZ_sub,ZT.toZ_ofNat,re_plane]
  unfold circleDen GaussianRationalCircleParametrization.denominator
  ipra_simps
  linear_combination (𝔞(S)+𝔞(x))*gap

theorem cross_im (x V b S e : PTm n) (hGap : Γ ⊢[PRAAx] S*S ≐ x*x+V*V+e) :
    ZT.toZ Γ (im (cross x V b S)) = ZT.toZ Γ (sign b)*𝔞(V*e) := by
  have gap := natEq hGap
  simp only [cross,im_sub,im_scale,circleNum,GaussianRationalCircleParametrization.im_numerator,
    GaussianRationalCircleParametrization.imagNumerator,ZT.toZ_sub,ZT.toZ_ofNat,im_plane]
  unfold circleDen GaussianRationalCircleParametrization.denominator sign GaussianRationalCircleParametrization.four
  simp only [ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination (1-2*𝔞(b))*𝔞(V)*gap

/-- The actual circle cross-error, with its exact original denominator.
The only mathematical inputs are the bit domain and the disk deficit. -/
theorem cross_norm (x V b S e : PTm n) (hb : Γ ⊢[PRAAx] bit b)
    (hGap : Γ ⊢[PRAAx] S*S ≐ x*x+V*V+e) : Γ ⊢[PRAAx]
    normSq (cross x V b S) ≐ circleDen x V S*e*e := by
  refine .orE hb ?_ ?_
  · have eb := natEq (Prf.hyp0 : (b ≐ zero)::Γ ⊢[PRAAx] b ≐ zero)
    apply deriveNat
    rw [normSq_eval,cross_re x V b S e hGap.wk,cross_im x V b S e hGap.wk]
    simp only [sign,ZT.toZ_sub,ZT.toZ_ofNat]
    unfold circleDen GaussianRationalCircleParametrization.denominator
    ipra_simps
    rw [eb]
    ring

  · have eb := natEq (Prf.hyp0 : (b ≐ one)::Γ ⊢[PRAAx] b ≐ one)
    apply deriveNat
    rw [normSq_eval,cross_re x V b S e hGap.wk,cross_im x V b S e hGap.wk]
    simp only [sign,ZT.toZ_sub,ZT.toZ_ofNat]
    unfold circleDen GaussianRationalCircleParametrization.denominator
    ipra_simps
    rw [eb]
    ring

def turn (r a : PTm n) : PTm n := code (sign r*re a) (sign r*im a)

@[simp] theorem subst_turn {m : ℕ} (σ : Fin n → PTm m) (r a : PTm n) :
    Syn.subst σ (turn r a) = turn (Syn.subst σ r) (Syn.subst σ a) := by simp [turn]

theorem re_turn (r a : PTm n) : ZT.toZ Γ (re (turn r a)) = ZT.toZ Γ (sign r)*ZT.toZ Γ (re a) := by
  rw [turn,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_mul]
theorem im_turn (r a : PTm n) : ZT.toZ Γ (im (turn r a)) = ZT.toZ Γ (sign r)*ZT.toZ Γ (im a) := by
  rw [turn,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_mul]

theorem sign_square (r : PTm n) (hr : Γ ⊢[PRAAx] bit r) : ZT.toZ Γ (sign r)*ZT.toZ Γ (sign r) = 1 := by
  have result : Γ ⊢[PRAAx] ZT.eq (sign r*sign r) (ZT.ofNat one) := by
    refine .orE hr ?_ ?_
    · apply ZT.derive
      have e := natEq (Prf.hyp0 : (r ≐ zero)::Γ ⊢[PRAAx] r ≐ zero)
      simp only [sign,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
      ipra_simps
      rw [e]
      ring
    · apply ZT.derive
      have e := natEq (Prf.hyp0 : (r ≐ one)::Γ ⊢[PRAAx] r ≐ one)
      simp only [sign,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
      ipra_simps
      rw [e]
      ring
  simpa only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_succ,Q.mk_zero,map_add,map_one,map_zero,_root_.zero_add] using ZT.toZ_eq result

theorem turn_twice (r a : PTm n) (hr : Γ ⊢[PRAAx] bit r) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (turn r (turn r a)) a := by
  apply GaussianRootAlgebra.equal_of_values
  · rw [re_turn,re_turn,← _root_.mul_assoc,sign_square r hr,_root_.one_mul]
  · rw [im_turn,im_turn,← _root_.mul_assoc,sign_square r hr,_root_.one_mul]

theorem turn_norm (r a : PTm n) (hr : Γ ⊢[PRAAx] bit r) : Γ ⊢[PRAAx] normSq (turn r a) ≐ normSq a := by
  apply deriveNat
  rw [normSq_eval,re_turn,im_turn,normSq_eval]
  calc
    _ = (ZT.toZ Γ (sign r)*ZT.toZ Γ (sign r))*(ZT.toZ Γ (re a)*ZT.toZ Γ (re a)+ZT.toZ Γ (im a)*ZT.toZ Γ (im a)) := by ring
    _ = _ := by rw [sign_square r hr,_root_.one_mul]; ring

theorem circleDen_lower (x V S : PTm n) : Γ ⊢[PRAAx] le (S*S) (circleDen x V S) :=
  le_trans (sq_le_sq (le_add_right S x)) (le_add_right _ _)

theorem circleDen_positive (x V S : PTm n) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx] le one (circleDen x V S) :=
  GaussianRationalCircleParametrization.denominator_positive _ _ (le_trans hS (le_add_right _ _))

def rotatedPoint (x V b S r : PTm n) : PTm n := GaussianRationalHorner.ofGaussian (turn r (circleNum x V b S)) (circleDen x V S)
def rotatedTarget (x V b S r : PTm n) : PTm n := GaussianRationalHorner.ofGaussian (turn r (plane x V b)) S
def rotatedCross (x V b S r : PTm n) : PTm n := sub (scale S (turn r (circleNum x V b S)))
  (scale (circleDen x V S) (turn r (plane x V b)))

@[simp] theorem subst_rotatedPoint {m : ℕ} (σ : Fin n → PTm m) (x V b S r : PTm n) :
    Syn.subst σ (rotatedPoint x V b S r) = rotatedPoint (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ b) (Syn.subst σ S) (Syn.subst σ r) := by simp [rotatedPoint]
@[simp] theorem subst_rotatedTarget {m : ℕ} (σ : Fin n → PTm m) (x V b S r : PTm n) :
    Syn.subst σ (rotatedTarget x V b S r) = rotatedTarget (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ b) (Syn.subst σ S) (Syn.subst σ r) := by simp [rotatedTarget]
@[simp] theorem subst_rotatedCross {m : ℕ} (σ : Fin n → PTm m) (x V b S r : PTm n) :
    Syn.subst σ (rotatedCross x V b S r) = rotatedCross (Syn.subst σ x) (Syn.subst σ V) (Syn.subst σ b) (Syn.subst σ S) (Syn.subst σ r) := by simp [rotatedCross]

theorem rotated_cross_norm (x V b S e r : PTm n) (hb : Γ ⊢[PRAAx] bit b) (hr : Γ ⊢[PRAAx] bit r)
    (hGap : Γ ⊢[PRAAx] S*S ≐ x*x+V*V+e) : Γ ⊢[PRAAx]
    normSq (rotatedCross x V b S r) ≐ circleDen x V S*e*e := by
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (rotatedCross x V b S r) (turn r (cross x V b S)) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [rotatedCross,cross,re_turn,re_sub,re_scale]; ring
    · simp only [rotatedCross,cross,im_turn,im_sub,im_scale]; ring
  exact (GaussianRootAlgebra.normSq_equal same).eqTrans ((turn_norm _ _ hr).eqTrans (cross_norm x V b S e hb hGap))

/-- The squared projection error is obtained from the actual integer
deficit and its numerical budget, with no distance or unit premise. -/
theorem rotated_squared_error (x V b S e H r : PTm n) (hb : Γ ⊢[PRAAx] bit b) (hr : Γ ⊢[PRAAx] bit r)
    (hS : Γ ⊢[PRAAx] le one S) (hH : Γ ⊢[PRAAx] le one H)
    (hGap : Γ ⊢[PRAAx] S*S ≐ x*x+V*V+e) (hBudget : Γ ⊢[PRAAx] le (H*e) (GaussianRationalCircleParametrization.four*S*S)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (GaussianRationalMetric.qnormSq (GaussianRationalMetric.qsub (rotatedPoint x V b S r) (rotatedTarget x V b S r)))
      (GaussianEuclideanDistanceName.fraction GaussianRationalCircleParametrization.four H) := by
  have hD := circleDen_positive (Γ := Γ) x V S hS
  have hDS := GaussianRationalHorner.positive_product _ _ hD hS
  have p := GaussianRationalHorner.represents_rescale _ _ _ S (GaussianRationalHorner.ofGaussian_represents (turn r (circleNum x V b S)) (circleDen x V S) hD)
  have q := GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
    (GaussianRationalHorner.represents_rescale _ _ _ (circleDen x V S) (GaussianRationalHorner.ofGaussian_represents (turn r (plane x V b)) S hS))
  have difference := GaussianRationalMetric.qsub_represents _ _ _ _ _ hDS p q
  have eS : Γ ⊢[PRAAx] le e (S*S) := le_of_eq_add (d := x*x+V*V) (hGap.eqTrans (add_comm _ _))
  have eD := le_trans eS (circleDen_lower x V S)
  have first := mul_le_mul_right (circleDen x V S*e) hBudget
  have second := mul_le_mul_right (GaussianRationalCircleParametrization.four*S*S*circleDen x V S) eD
  have bound : Γ ⊢[PRAAx] le (H*normSq (rotatedCross x V b S r))
      (GaussianRationalCircleParametrization.four*((circleDen x V S*S)*(circleDen x V S*S))) := by
    apply le_congr (congrMul (.eqRefl H) (rotated_cross_norm x V b S e r hb hr hGap)).eqSymm (.eqRefl _)
    have h1 : Γ ⊢[PRAAx] le (H*(circleDen x V S*e*e))
        (GaussianRationalCircleParametrization.four*S*S*circleDen x V S*e) :=
      le_congr (by ipra_ring) (by ipra_ring) first
    have h2 : Γ ⊢[PRAAx] le (GaussianRationalCircleParametrization.four*S*S*circleDen x V S*e)
        (GaussianRationalCircleParametrization.four*((circleDen x V S*S)*(circleDen x V S*S))) :=
      le_congr (by ipra_ring) (by ipra_ring) second
    exact le_trans h1 h2
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ hDS hDS) hH
    (GaussianRationalMetric.qnormSq_represents _ _ _ hDS difference)
    (GaussianEuclideanDistanceName.fraction_represents _ _ hH) bound

theorem rotated_point_canonical (x V b S r : PTm n) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (rotatedPoint x V b S r) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (circleDen_positive x V S hS)

theorem rotated_point_unit (x V b S r : PTm n) (hb : Γ ⊢[PRAAx] bit b) (hr : Γ ⊢[PRAAx] bit r)
    (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (rotatedPoint x V b S r) ≐ GaussianEuclideanDistanceName.fraction one one := by
  have hp := circleDen_positive (Γ := Γ) x V S hS
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (GaussianRationalMetric.qnormSq_represents _ _ _ hp (GaussianRationalHorner.ofGaussian_represents _ _ hp))
    (GaussianEuclideanDistanceName.fraction_represents one one (le_refl one))
    (GaussianRationalHorner.positive_product _ _ hp hp) (le_refl one)
  apply ZT.derive
  have value := natEq ((turn_norm r (circleNum x V b S) hr).eqTrans
    (GaussianRationalCircleParametrization.numerator_norm (S+x) V b hb))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [circleDen]
  ipra_simps
  rw [value]
  ring

def pointF : PR 5 := PTm.toPR (rotatedPoint (var 0) (var 1) (var 2) (var 3) (var 4))
theorem point_program (x V b S r : PTm n) : Γ ⊢[PRAAx]
    PTm.app pointF ![x,V,b,S,r] ≐ rotatedPoint x V b S r := by
  simpa [pointF] using toPR_eq (Γ := Γ) (rotatedPoint (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![x,V,b,S,r]

theorem actual_cross_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bit (var 2) ⟶ var 3*var 3 ≐ var 0*var 0+var 1*var 1+var 4 ⟶
      normSq (cross (var 0) (var 1) (var 2) (var 3)) ≐ circleDen (var 0) (var 1) (var 3)*var 4*var 4) :=
  closeUniv 5 (.impI (.impI (cross_norm _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rotation_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (bit (var 0) ⟶ normSq (turn (var 0) (var 1)) ≐ normSq (var 1)) :=
  closeUniv 2 (.impI (turn_norm _ _ Prf.hyp0))

theorem actual_rotated_projection_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bit (var 2) ⟶ bit (var 4) ⟶ le one (var 3) ⟶
      (GaussianRationalHorner.canonical (rotatedPoint (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        GaussianRationalMetric.qnormSq (rotatedPoint (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ GaussianEuclideanDistanceName.fraction one one)) :=
  closeUniv 5 (.impI (.impI (.impI (.andI (rotated_point_canonical _ _ _ _ _ Prf.hyp0)
    (rotated_point_unit _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_projection_squared_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (bit (var 2) ⟶ bit (var 6) ⟶ le one (var 3) ⟶ le one (var 5) ⟶
      var 3*var 3 ≐ var 0*var 0+var 1*var 1+var 4 ⟶
      le (var 5*var 4) (GaussianRationalCircleParametrization.four*var 3*var 3) ⟶
      RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq
        (GaussianRationalMetric.qsub (rotatedPoint (var 0) (var 1) (var 2) (var 3) (var 6))
          (rotatedTarget (var 0) (var 1) (var 2) (var 3) (var 6))))
        (GaussianEuclideanDistanceName.fraction GaussianRationalCircleParametrization.four (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (rotated_squared_error _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem actual_projection_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app pointF ![var 0,var 1,var 2,var 3,var 4] ≐ rotatedPoint (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (point_program _ _ _ _ _)


end LeanProofs.IPRA.Analysis.GaussianIntegerCircleProjection
