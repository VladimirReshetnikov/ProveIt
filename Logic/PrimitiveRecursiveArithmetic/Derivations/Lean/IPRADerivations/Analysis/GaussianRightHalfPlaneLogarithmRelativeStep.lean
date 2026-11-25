import IPRADerivations.Analysis.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.GaussianLocalLogarithmLinearRemainder
import IPRADerivations.Analysis.GaussianEulerBetaProductPascal

/-!
# Relative increments for right-half-plane logarithms

For two encoded Gaussian rationals on a common denominator, the relative
step has literal numerator `(v-u) conj(u)` and denominator `|u|²`.
A numerical bound on the original displacement gives an admissible
Mercator radius and a quadratic remainder in terms of the base real
numerator. The exact rational product recovers the later input.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRelativeStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq normSq_eval normSq_scale scale mul add oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFiniteLogarithmCompositionTail (linearValue)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianLocalLogarithmName (point)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents
  qmul qmul_canonical qmul_represents qadd_canonical qadd_represents
  canonical_unique positive_product represents_rescale represents_congr)
open GaussianRationalMetric (distanceBounded qsub qsub_represents qsub_canonical)
open GaussianRationalReciprocal (conjugate norm_conjugate qone qone_represents_scaled re_conjugate im_conjugate)
open GaussianRootAlgebra (sub equal equal_of_values equal_refl normSq_equal
  re_add im_add re_mul im_mul re_sub im_sub re_scale im_scale re_one im_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (u v : PTm n) : PTm n := mul (sub v u) (conjugate u)
def denominator (u : PTm n) : PTm n := normSq u
def relative (u v : PTm n) : PTm n := ofGaussian (numerator u v) (denominator u)
def radius (A B H : PTm n) : PTm n := H*(A+B)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (u v : PTm n) :
    Syn.subst σ (numerator u v) = numerator (Syn.subst σ u) (Syn.subst σ v) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (u : PTm n) :
    Syn.subst σ (denominator u) = denominator (Syn.subst σ u) := by simp [denominator]
@[simp] theorem subst_relative {m : ℕ} (σ : Fin n → PTm m) (u v : PTm n) :
    Syn.subst σ (relative u v) = relative (Syn.subst σ u) (Syn.subst σ v) := by simp [relative]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (A B H : PTm n) :
    Syn.subst σ (radius A B H) = radius (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ H) := by simp [radius]

private theorem native_lower (A B neg : PTm n) (hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneArgument.source A neg) :
    Γ ⊢[PRAAx] le (A*A) (denominator (native A B neg)) :=
  le_congr (.eqRefl _) (native_norm A B neg hs.andE₂).eqSymm (le_add_right _ _)

theorem denominator_positive (A B neg : PTm n) (hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneArgument.source A neg) :
    Γ ⊢[PRAAx] le one (denominator (native A B neg)) :=
  le_trans (positive_product _ _ hs.andE₁ hs.andE₁) (native_lower A B neg hs)

private theorem twice_norm (A B : PTm n) : Γ ⊢[PRAAx] le ((A+B)*A) (two*(A*A+B*B)) := by
  have cross : Γ ⊢[PRAAx] le (A*B) (A*A+B*B) := by
    refine .orE (le_total A B) ?_ ?_
    · exact le_trans (le_mul_mono Prf.hyp0 (le_refl B)) (le_add_left _ _)
    · exact le_trans (le_mul_mono (le_refl A) Prf.hyp0) (le_add_right _ _)
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_add_right (A*A) (B*B)) cross)

theorem paid_radius (A B neg H : PTm n) (hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneArgument.source A neg) :
    Γ ⊢[PRAAx] le (radius A B H*A) (two*H*denominator (native A B neg)) := by
  exact le_congr (by unfold radius; ipra_ring)
    (by unfold denominator; ipra_ring)
    (le_mul_mono (le_refl H)
      (le_congr (.eqRefl _) (congrMul (.eqRefl two) (native_norm A B neg hs.andE₂)).eqSymm
        (twice_norm A B)))

theorem mercator_source (A B neg v H : PTm n) (hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneArgument.source A neg)
    (hstep : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub v (native A B neg)) H)
    (hsmall : Γ ⊢[PRAAx] le (num 4*H) A) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source (numerator (native A B neg) v) (radius A B H)
      (denominator (native A B neg)) := by
  let u := native A B neg
  let R := radius A B H
  let N := denominator u
  have raw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (conjugate u) (A+B) :=
    le_congr ((norm_conjugate u).eqTrans (native_norm A B neg hs.andE₂)).eqSymm (.eqRefl _)
      (le_of_eq_add (d := A*B+B*A) (by ipra_ring))
  have product : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (numerator u v) R :=
    ComplexLogarithmRemainder.bounded_mul hstep raw
  have upper : Γ ⊢[PRAAx] le (A*(two*R)) (A*N) := by
    have hp := paid_radius A B neg H hs
    have left : Γ ⊢[PRAAx] le (A*(two*R)) (num 4*H*N) :=
      le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl two) hp)
    exact le_trans left (le_mul_mono hsmall (le_refl N))
  exact .andI (denominator_positive A B neg hs) (.andI product (cancel_pos hs.andE₁ upper))

theorem quadratic_error (p A B neg v H : PTm n) (hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneArgument.source A neg)
    (hstep : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub v (native A B neg)) H)
    (hsmall : Γ ⊢[PRAAx] le (num 4*H) A) :
    Γ ⊢[PRAAx] distanceBounded
      (point p (numerator (native A B neg) v) (radius A B H) (denominator (native A B neg)))
      (relative (native A B neg) v) (num 4*H*H*unit p+A*A) (A*A*unit p) := by
  let N := denominator (native A B neg)
  let R := radius A B H
  let U := unit p
  have hN := denominator_positive A B neg hs
  have hQ := positive_product _ _ (positive_product _ _ hN hN) (unit_positive p)
  have hT := positive_product _ _ (positive_product _ _ hs.andE₁ hs.andE₁) (unit_positive p)
  have rate := paid_radius A B neg H hs
  have squared := le_mul_mono rate rate
  exact distance_radius_mono _ _ (R*R*U+N*N) (N*N*U) (num 4*H*H*U+A*A) (A*A*U) hQ hT
    (by ipra_le 𝔞(U)^2*sl squared)
    (GaussianLocalLogarithmLinearRemainder.original_linear_remainder p _ R N (mercator_source A B neg v H hs hstep hsmall))

private theorem displacement_code (u v D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qsub (ofGaussian v D) (ofGaussian u D) ≐ ofGaussian (sub v u) D :=
  canonical_unique _ _ _ _ (qsub_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (qsub_represents _ _ _ _ _ hD (ofGaussian_represents _ _ hD) (ofGaussian_represents _ _ hD))
    (ofGaussian_represents _ _ hD)

private theorem raw_norm_positive (u D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] le one (denominator u)) :
    Γ ⊢[PRAAx] le one (GaussianRationalReciprocal.normNumerator (ofGaussian u D)) := by
  let q := ofGaussian u D
  let b := GaussianRationalL1.rawDen q
  let v := GaussianRationalL1.rawGaussian q
  let M := normSq v
  have cross := GaussianDominantPairAlgebra.represents_cross q u v D b
    (ofGaussian_represents u D hD) (GaussianRationalL1.raw_represents q)
  have eq := (normSq_scale b u).eqSymm.eqTrans ((normSq_equal cross).eqTrans (normSq_scale D v))
  have hB := GaussianRationalL1.raw_den_positive (Γ := Γ) q
  have pos := positive_product (b*b) (normSq u) (positive_product _ _ hB hB) hu
  refine .orE (zero_or_succ M) ?_ ?_
  · have bz : ((M ≐ zero) :: Γ) ⊢[PRAAx] (D*D)*M ≐ zero :=
      (congrMul (.eqRefl _) Prf.hyp0).eqTrans (by ipra_ring)
    have bad := le_congr (.eqRefl one) (eq.wk.eqTrans bz) pos.wk
    exact .botE _ (succ_ne_zero ((succ_add zero _).eqSymm.eqTrans (eq_add_of_le bad).eqSymm))
  · exact le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ _)

private theorem inverse_code (u D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] le one (denominator u)) :
    Γ ⊢[PRAAx] GaussianRationalReciprocal.reciprocal (ofGaussian u D) ≐
      ofGaussian (scale D (conjugate u)) (denominator u) := by
  let q := ofGaussian u D
  let v := ofGaussian (scale D (conjugate u)) (denominator u)
  have rep := qmul_represents q v u (scale D (conjugate u)) D (denominator u) hD hu
    (ofGaussian_represents u D hD) (ofGaussian_represents _ _ hu)
  have transformed := represents_congr (.eqRefl _) (GaussianRationalReciprocal.scaled_conjugate_product u D)
    (.eqRefl _) rep
  have inverse := canonical_unique _ _ _ _ (qmul_canonical _ _) GaussianRationalSyntheticDivision.qone_canonical
    (positive_product _ _ hD hu) transformed (qone_represents_scaled _)
  exact GaussianEulerBetaProductPascal.inverse_unique q _ v
    (GaussianRationalReciprocal.reciprocal_canonical q) (ofGaussian_canonical _ _ hu)
    (GaussianRationalReciprocal.reciprocal_identity q (raw_norm_positive u D hD hu)) inverse

theorem relative_binding (u v D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hu : Γ ⊢[PRAAx] le one (denominator u)) :
    Γ ⊢[PRAAx] qmul (qsub (ofGaussian v D) (ofGaussian u D))
      (GaussianRationalReciprocal.reciprocal (ofGaussian u D)) ≐ relative u v := by
  let w := ofGaussian (sub v u) D
  let U := ofGaussian (scale D (conjugate u)) (denominator u)
  have first := GaussianRationalSyntheticDivision.qmul_congr (displacement_code u v D hD) (inverse_code u D hD hu)
  have prod := qmul_represents w U (sub v u) (scale D (conjugate u)) D (denominator u) hD hu
    (ofGaussian_represents _ _ hD) (ofGaussian_represents _ _ hu)
  have left : Γ ⊢[PRAAx] equal (mul (sub v u) (scale D (conjugate u))) (scale D (numerator u v)) := by
    apply equal_of_values <;> simp only [numerator,re_mul,im_mul,re_scale,im_scale] <;> ring
  have right := represents_rescale _ _ _ D (ofGaussian_represents (numerator u v) (denominator u) hu)
  exact first.eqTrans (canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ hu)
    (positive_product _ _ hD hu) (represents_congr (.eqRefl _) left (.eqRefl _) prod)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm (denominator u) D) right))

theorem factor_binding (u v D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hu : Γ ⊢[PRAAx] le one (denominator u)) :
    Γ ⊢[PRAAx] qmul (ofGaussian u D) (linearValue (relative u v)) ≐ ofGaussian v D := by
  let a := ofGaussian u D
  let b := ofGaussian v D
  let d := qsub b a
  let c := GaussianRationalReciprocal.reciprocal a
  have ac := ofGaussian_canonical u D hD
  have bc := ofGaussian_canonical v D hD
  have dc := qsub_canonical b a (Γ := Γ)
  have base := GaussianRationalReciprocal.reciprocal_identity a (raw_norm_positive u D hD hu)
  have product : Γ ⊢[PRAAx] qmul a (relative u v) ≐ d := by
    have bind := GaussianRationalSyntheticDivision.qmul_congr (.eqRefl a) (relative_binding u v D hD hu).eqSymm
    have move := (GaussianReciprocalHorner.qmul_associative (Γ := Γ) a d c).eqSymm.eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative a d) (.eqRefl c))
    have inv := (GaussianReciprocalHorner.qmul_associative d a c).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl d) base)
    exact bind.eqTrans (move.eqTrans (inv.eqTrans (GaussianReciprocalHorner.qmul_one_right d dc)))
  have split := GaussianRationalCoefficientScaling.qmul_add (Γ := Γ) a qone (relative u v)
  have reduced := GaussianRationalSyntheticDivision.qadd_congr (GaussianReciprocalHorner.qmul_one_right a ac) product
  have dr := represents_congr (displacement_code u v D hD).eqSymm (equal_refl _) (.eqRefl _)
    (ofGaussian_represents (sub v u) D hD)
  have sum := qadd_represents a d u (sub v u) D hD (ofGaussian_represents u D hD) dr
  have add_back : Γ ⊢[PRAAx] equal (add u (sub v u)) v := by
    apply equal_of_values <;> simp only [re_add,im_add,re_sub,im_sub] <;> ring
  have back := canonical_unique _ _ v D (qadd_canonical a d) bc hD
    (represents_congr (.eqRefl _) add_back (.eqRefl _) sum) (ofGaussian_represents v D hD)
  exact split.eqTrans (reduced.eqTrans back)

theorem actual_right_half_plane_relative_Mercator_quadratic_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((GaussianRightHalfPlaneArgument.source (var 0) (var 2) ⋏
        (ComplexLogarithmRemainder.bounded (sub (var 3) (native (var 0) (var 1) (var 2))) (var 4) ⋏
          le (num 4*var 4) (var 0))) ⟶
        distanceBounded (point (var 5) (numerator (native (var 0) (var 1) (var 2)) (var 3))
            (radius (var 0) (var 1) (var 4)) (denominator (native (var 0) (var 1) (var 2))))
          (relative (native (var 0) (var 1) (var 2)) (var 3))
          (num 4*var 4*var 4*unit (var 5)+var 0*var 0) (var 0*var 0*unit (var 5))) :=
  closeUniv 6 (.impI (quadratic_error _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRelativeStep
