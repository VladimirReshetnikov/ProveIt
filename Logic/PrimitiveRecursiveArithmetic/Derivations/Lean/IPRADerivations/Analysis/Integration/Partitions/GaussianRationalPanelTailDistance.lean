import IPRADerivations.Analysis.FiniteOperations.GaussianPositiveRadiusFiniteSum
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveExponentialOrder

/-!
# Finite observed-value tail estimates for actual complex panels

The middle term cancels by original normalized arithmetic even when its
raw encoding is not canonical. Positive real companion bounds control
the sum of both tails; one actual companion split and outer/inner gap
therefore bound the complex outer/inner gap with all three original
rational tolerances retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPanelTailDistance

open_ipra
open GaussianRationalHorner (qadd qadd_canonical qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianPositiveRadiusFiniteSum (boundBy add_bound enlarge_radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def threeSum (left middle right : PTm n) : PTm n := qadd left (qadd middle right)
ipra_subst threeSum

theorem middle_difference (left middle right : PTm n) : Γ ⊢[PRAAx]
    qsub (threeSum left middle right) middle ≐ qadd left right := by
  have rearranged : Γ ⊢[PRAAx] threeSum left middle right ≐ qadd middle (qadd left right) :=
    (qadd_associative left middle right).eqSymm.eqTrans
      ((qadd_congr (qadd_commutative left middle) (.eqRefl _)).eqTrans (qadd_associative middle left right))
  exact (qsub_congr rearranged (.eqRefl _)).eqTrans (qadd_sub_cancel middle _ (qadd_canonical left right))

theorem triangle (x y z P Q S T : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) (hT : Γ ⊢[PRAAx] le one T)
    (hxy : Γ ⊢[PRAAx] distanceBounded x y P Q) (hyz : Γ ⊢[PRAAx] distanceBounded y z S T) : Γ ⊢[PRAAx]
    distanceBounded x z (P*T+S*Q) (Q*T) := by
  have d := positive_product _ _ hQ hT
  exact distance_triangle_same _ _ _ _ _ _ d
    (distance_radius_mono _ _ _ _ _ _ hQ d (le_of_eq_add (d := zero) (by ipra_ring)) hxy)
    (distance_radius_mono _ _ _ _ _ _ hT d (le_of_eq_add (d := zero) (by ipra_ring)) hyz)

theorem original_tail_distance (outer middle left right P Q S T : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] distanceBounded outer (threeSum left middle right) P Q)
    (tails : Γ ⊢[PRAAx] bounded (qadd left right) S T) : Γ ⊢[PRAAx]
    distanceBounded outer middle (P*T+S*Q) (Q*T) :=
  triangle _ _ _ _ _ _ _ hQ hT h
    (GaussianRationalReciprocal.bound_congr (middle_difference left middle right).eqSymm (.eqRefl _) (.eqRefl _) tails)

private theorem real_zero : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (qzero : PTm n)) (ZT.ofNat zero) one :=
  GaussianRationalHorner.scalar_congr (.eqRefl _)
    (ZT.derive (by rw [GaussianRootAlgebra.re_zero,ZT.toZ_ofNat]; ipra_simps)) (.eqRefl _)
    (GaussianRationalHorner.zero_represents one).andE₁

/-- The domination relation carries its genuine positive real radius;
an actual norm bound on that radius therefore bounds the original value. -/
theorem dominated_bound (z r S T : PTm n) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] boundBy z r) (hr : Γ ⊢[PRAAx] bounded r S T) : Γ ⊢[PRAAx] bounded z S T := by
  have near := (GaussianReconstructionRoots.distance_zero_iff r S T hT).iffMpr hr
  have scalar := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hT near)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (enlarge_radius z r (fstT qzero) zero one S T h (le_refl one) hT real_zero scalar)

/-- Direct signed scalar control is available when the caller already
has the actual sum of its corrected real companion observations. -/
theorem dominated_upper (z r P Q A B : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] boundBy z r)
    (hu : Γ ⊢[PRAAx] RationalValueBounds.upper (fstT r) (GaussianEuclideanDistanceName.fraction P Q) A B) : Γ ⊢[PRAAx]
    bounded z (P*B+A*Q) (Q*B) :=
  enlarge_radius z r _ P Q A B h hQ hB (GaussianEuclideanDistanceName.fraction_represents P Q hQ) hu

theorem original_companion_split_distance (fO fM fL fR gO gM gL gR P Q A B C D : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] distanceBounded fO (threeSum fL fM fR) P Q)
    (hl : Γ ⊢[PRAAx] boundBy fL gL) (hr : Γ ⊢[PRAAx] boundBy fR gR)
    (hg : Γ ⊢[PRAAx] distanceBounded gO (threeSum gL gM gR) A B)
    (gap : Γ ⊢[PRAAx] distanceBounded gO gM C D) : Γ ⊢[PRAAx]
    distanceBounded fO fM (P*(B*D)+(A*D+C*B)*Q) (Q*(B*D)) := by
  have near := triangle (threeSum gL gM gR) gO gM A B C D hB hD (distance_symmetric _ _ _ _ hB hg) gap
  have tails : Γ ⊢[PRAAx] bounded (qadd gL gR) (A*D+C*B) (B*D) :=
    GaussianRationalReciprocal.bound_congr (middle_difference gL gM gR) (.eqRefl _) (.eqRefl _) near
  have bound := dominated_bound _ _ _ _ (positive_product _ _ hB hD) (add_bound _ _ _ _ hl hr) tails
  exact original_tail_distance _ _ _ _ _ _ _ _ hQ (positive_product _ _ hB hD) hf bound

theorem actual_raw_panel_middle_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qsub (threeSum (var 0) (var 1) (var 2)) (var 1) ≐ qadd (var 0) (var 2)) :=
  closeUniv 3 (middle_difference _ _ _)

theorem actual_observed_companion_panel_tail_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (((le one (var 9) ⋏ (le one (var 11) ⋏ le one (var 13))) ⋏
      (distanceBounded (var 0) (threeSum (var 2) (var 1) (var 3)) (var 8) (var 9) ⋏
        (boundBy (var 2) (var 6) ⋏ (boundBy (var 3) (var 7) ⋏
          (distanceBounded (var 4) (threeSum (var 6) (var 5) (var 7)) (var 10) (var 11) ⋏
            distanceBounded (var 4) (var 5) (var 12) (var 13)))))) ⟶
      distanceBounded (var 0) (var 1)
        (var 8*(var 11*var 13)+(var 10*var 13+var 12*var 11)*var 9) (var 9*(var 11*var 13))) :=
  closeUniv 14 (.impI (original_companion_split_distance _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalPanelTailDistance
