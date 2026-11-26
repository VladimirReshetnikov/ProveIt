import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNameBounds

/-!
# Exact order operations for the original Gaussian-rational metric

Symmetry is proved for arbitrary original point codes by transporting their
actual representations to a computed positive common denominator. Radius
monotonicity compares the original squared rational tolerances. Neither
operation requires canonical original operands or a supplied normalization.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric
  (bounded distanceBounded qsub qnegative qsub_represents qnegative_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (canonical_unique represents_congr positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalL1
  (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (rescale_to qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal_of_values re_sub im_sub re_neg im_neg)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem distance_congr {z z' w w' A A' B B' : PTm n}
    (hz : Γ ⊢[PRAAx] z ≐ z') (hw : Γ ⊢[PRAAx] w ≐ w')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] distanceBounded z w A B) : Γ ⊢[PRAAx] distanceBounded z' w' A' B' :=
  bound_congr (qsub_congr hz hw) hA hB h

theorem reversed_difference (z w : PTm n) : Γ ⊢[PRAAx]
    qnegative (qsub z w) ≐ qsub w z := by
  let E := rawDen z*rawDen w
  let a := scale (rawDen w) (rawGaussian z)
  let b := scale (rawDen z) (rawGaussian w)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive z) (raw_den_positive w)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (rawDen w) E (raw_represents (Γ := Γ) z)
    (.eqRefl _)
  have hw := rescale_to w (rawGaussian w) (rawDen w) (rawDen z) E (raw_represents (Γ := Γ) w)
    (by unfold E; ipra_ring)
  have lhs := qnegative_represents _ _ _ (qsub_represents z w a b E hE hz hw)
  have rhs := qsub_represents w z b a E hE hw hz
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qnegative_canonical _)
    (GaussianRationalMetric.qsub_canonical _ _) hE (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_neg,im_neg,re_sub,im_sub] <;> ring

theorem distance_symmetric (z w A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded z w A B) : Γ ⊢[PRAAx] distanceBounded w z A B :=
  bound_congr (reversed_difference z w) (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ hB h)

theorem distance_radius_mono (z w A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hrad : Γ ⊢[PRAAx] le (A*D) (C*B))
    (h : Γ ⊢[PRAAx] distanceBounded z w A B) : Γ ⊢[PRAAx] distanceBounded z w C D :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hB hD hrad h

/-- If both observation denominators are at least D, their two errors add to
at most 2/D. The order of the two observations is arbitrary. -/
theorem distance_two_errors (z w B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hDB : Γ ⊢[PRAAx] le D B) (hDC : Γ ⊢[PRAAx] le D C)
    (h : Γ ⊢[PRAAx] distanceBounded z w (B+C) (B*C)) : Γ ⊢[PRAAx] distanceBounded z w two D := by
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hB hC) hD _ h
  exact le_congr (by ipra_ring) (by ipra_ring)
    (add_le_add₂ (mul_le_mul_right B hDC) (mul_le_mul_right C hDB))

/-- Combine two ordered cases for independent observations, reversing the
samples and the radius factors in the second case. -/
theorem distance_of_ordered_observations (z w p q : PTm n)
    (hpq : le p q :: Γ ⊢[PRAAx] distanceBounded z w (unit p+unit q) (unit p*unit q))
    (hqp : le q p :: Γ ⊢[PRAAx] distanceBounded w z (unit q+unit p) (unit q*unit p)) :
    Γ ⊢[PRAAx] distanceBounded z w (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) hpq ?_
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) hqp)

/-- A later observation within one unit of the earlier precision gives the
usual symmetric two-clock comparison. -/
theorem distance_from_later_observations (z w p q : PTm n)
    (hpq : le p q :: Γ ⊢[PRAAx] distanceBounded w z one (unit p))
    (hqp : le q p :: Γ ⊢[PRAAx] distanceBounded z w one (unit q)) :
    Γ ⊢[PRAAx] distanceBounded z w (unit p+unit q) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hD := positive_product _ _ hp hq
  refine .orE (le_total p q) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ hp.wk hD.wk
      (le_of_eq_add (d := unit p*unit p) (by ipra_ring))
      (distance_symmetric _ _ _ _ hp.wk hpq)
  · exact distance_radius_mono _ _ _ _ _ _ hq.wk hD.wk
      (le_of_eq_add (d := unit q*unit q) (by ipra_ring)) hqp

theorem distance_triangle_same (z y w A C B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hzy : Γ ⊢[PRAAx] distanceBounded z y A B)
    (hyw : Γ ⊢[PRAAx] distanceBounded y w C B) : Γ ⊢[PRAAx]
    distanceBounded z w (A+C) B :=
  distance_radius_mono z w (A*B+C*B) (B*B) (A+C) B (positive_product _ _ hB hB) hB
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _))
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hB hB hzy hyw)

/-- Combine the two end observations with a comparison at a shared auxiliary
precision. The two end comparisons contribute two auxiliary units in total. -/
theorem distance_through_auxiliary {x y z w : PTm n} (p q r A B C : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (left : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit r) (unit p*unit r))
    (middle : Γ ⊢[PRAAx] distanceBounded y z (A*unit r+C*B) (B*unit r))
    (right : Γ ⊢[PRAAx] distanceBounded z w (unit r+unit q) (unit r*unit q)) :
    Γ ⊢[PRAAx] distanceBounded x w
      ((A*unit p*unit q+B*(unit p+unit q))*unit r+(C+two)*(B*unit p*unit q))
      ((B*unit p*unit q)*unit r) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hr := unit_positive (Γ := Γ) r
  have dp := positive_product _ _ hp hr
  have dm := positive_product _ _ hB hr
  have dq := positive_product _ _ hr hq
  have first := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ dp dm left middle
  have both := positive_product _ _ dp dm
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ both dq first right
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ both dq)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hB hp) hq) hr)
    (le_of_eq_add (d := zero) (by ipra_ring)) joined

/-- The middle comparison is entirely paid at the auxiliary precision. -/
theorem distance_through_diagonal {x y z w : PTm n} (p q r K : PTm n)
    (left : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit r) (unit p*unit r))
    (middle : Γ ⊢[PRAAx] distanceBounded y z K (unit r))
    (right : Γ ⊢[PRAAx] distanceBounded z w (unit r+unit q) (unit r*unit q)) :
    Γ ⊢[PRAAx] distanceBounded x w
      ((unit p+unit q)*unit r+(K+two)*(unit p*unit q)) ((unit p*unit q)*unit r) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (distance_through_auxiliary p q r zero one K (le_refl one) left
      (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (one_mul _).eqSymm middle) right)

theorem original_distance_symmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ Fm.iff
      (distanceBounded (var 0) (var 1) (var 2) (var 3))
      (distanceBounded (var 1) (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.iffI
    (.impI (distance_symmetric _ _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (distance_symmetric _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem original_distance_radius_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶
      le (var 2*var 5) (var 4*var 3) ⟶
        distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
          distanceBounded (var 0) (var 1) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (distance_radius_mono _ _ _ _ _ _ (Prf.wk hyp2) hyp2 Prf.hyp1 Prf.hyp0)))))

theorem original_common_denominator_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ distanceBounded (var 0) (var 1) (var 3) (var 5) ⟶
      distanceBounded (var 1) (var 2) (var 4) (var 5) ⟶
        distanceBounded (var 0) (var 2) (var 3+var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI
    (distance_triangle_same _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
