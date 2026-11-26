import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.GaussianGammaNegativeIntervalLogThinChordReadback
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Unscaled negative log-absolute chord from a center rate

A certified center-to-base rate with denominator W*E pays for the W
in the thin chord. Removing the common auxiliary clock retains just
the leading K/E radius and the independent endpoint observation slacks.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogChordStationary

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData name_regular name_real)
open GaussianGammaNegativeIntervalLogThinChord (centerData margin)
open GaussianGammaNegativeIntervalLogThinChordReadback (budget difference_at)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (sum_right_error)
open GaussianNamedInverseRate (denominator_positive diagonal_rate independentRate rateNumerator rateDenominator)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (precision upperSlack remove_upper_slack)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd qzero ofGaussian_canonical positive_product)
open GaussianRationalLinearProduct (add_sub_right)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianStirlingTailComparison (point_add_upper_same point_order_refl)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_of_radius upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => nameF
local notation "lg" => nameData

def observationCost (a c b N W : PTm n) : PTm n := two*W+budget a c b N W

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (a c b N W : PTm n) :
    Syn.subst σ (observationCost a c b N W) =
      observationCost (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ W) := by
  simp [observationCost,two]

private theorem center_displacement (t a c b N W K E : PTm n) (hW : Γ ⊢[PRAAx] le two W)
    (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b N W) (lg a b N) K (W*E)) :
    Γ ⊢[PRAAx] distanceBounded
      (natScale W (qsub (ap2 G t (centerData a c b N W)) (ap2 G t (lg a b N)))) qzero
      (K*unit t+two*W*E) (E*unit t) := by
  let U := unit t
  let X := ap2 G t (lg a b N)
  let Z := ap2 G t (centerData a c b N W)
  let d := qsub Z X
  let den := (W*E)*U
  have hU := unit_positive (Γ := Γ) t
  have hWN := positive_product _ _ (le_trans RationalAlgebra.two_positive hW) hE
  have hDen : Γ ⊢[PRAAx] le one den := positive_product _ _ hWN hU
  have hNU := positive_product _ _ hE hU
  have small : Γ ⊢[PRAAx] bounded d (K*U+two*(W*E)) den :=
    diagonal_rate G G (centerData a c b N W) (lg a b N) K (W*E) t hWN h
  have product : Γ ⊢[PRAAx] bounded (natScale W d) (W*(K*U+two*(W*E))) den :=
    bound_congr (natScale_as_product W d).eqSymm (.eqRefl _) (one_mul den)
      (bounded_product _ _ _ _ _ _ (le_refl one) hDen (GaussianNamedNaturalScale.natural_point_bound W) small)
  have scaled : Γ ⊢[PRAAx] bounded (natScale W d) (K*U+two*W*E) (E*U) :=
    bounded_radius_mono _ _ _ _ _ hDen hNU (by unfold den; exact le_of_eq_add (d := zero) (by ipra_ring)) product
  exact (distance_zero_iff _ _ _ hNU).iffMpr scaled

/-- Before removing the auxiliary query, the only additional slack is
the fixed chord readback cost and twice the weight at that query. -/
theorem diagonal_at (t a c b N W K E : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b)
    (hW : Γ ⊢[PRAAx] le two W) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b N W) (lg a b N) K (W*E)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b) (ap2 G t (lg a b N)))) (fstT (ap2 G t (lg c b N)))
      (K*unit t+observationCost a c b N W*E) (E*unit t) := by
  let U := unit t
  let X := ap2 G t (lg a b N)
  let Y := ap2 G t (lg c b N)
  let Z := ap2 G t (centerData a c b N W)
  let g := margin a c b
  let d := natScale W (qsub Z X)
  let A := K*U+observationCost a c b N W*E
  let D := E*U
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE hU
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hB := positive_product _ _ RationalAlgebra.two_positive hb
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hg : Γ ⊢[PRAAx] GaussianRationalHorner.canonical g :=
    ofGaussian_canonical _ _ (positive_product _ _ (positive_product _ _ h4 hB) hB)
  have close : Γ ⊢[PRAAx] distanceBounded d qzero (K*U+two*W*E) D :=
    center_displacement t a c b N W K E hW hE h
  have move : Γ ⊢[PRAAx] distanceBounded g (qadd g d) (K*U+two*W*E) D :=
    distance_congr (qadd_zero_right g hg) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (sum_right_error g qzero d _ _ hD (distance_symmetric _ _ _ _ hD close))
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD move)
  have chord := difference_at t a c b N W ha hc hW
  have joined : Γ ⊢[PRAAx] upper (fstT g) (fstT (qsub Y X)) A D :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hD hU) (upper_triangle _ _ _ _ _ _ _ before chord)
      (le_of_eq_add (d := zero) (by unfold A D observationCost; ipra_ring))
  have id : Γ ⊢[PRAAx] upper (fstT X) (fstT X) zero D :=
    upper_of_order _ _ _ _ (point_order_refl _)
  have added := point_add_upper_same _ _ _ _ _ _ _ hD joined id
  have hy := (GaussianSignedNameExponentialOrder.real_sample_at G (lg c b N) t (name_real (Γ := Γ) c b N)).andE₁
  have read : Γ ⊢[PRAAx] qadd (qsub Y X) X ≐ Y :=
    (qadd_commutative (qsub Y X) X).eqTrans (add_sub_right X Y hy)
  exact upper_congr (.eqRefl _) (congrFst read) (LeanProofs.IPRA.add_zero A) (.eqRefl _) added

private theorem observation_slack (p q t a c b N W K E : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b)
    (hW : Γ ⊢[PRAAx] le two W) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b N W) (lg a b N) K (W*E)) :
    Γ ⊢[PRAAx] upperSlack (fstT (qadd (margin a c b) (ap2 G p (lg a b N)))) (fstT (ap2 G q (lg c b N)))
      (rateNumerator K E p q) (rateDenominator E p q) (observationCost a c b N W+two) t := by
  let P := unit p
  let Q := unit q
  let U := unit t
  let g := margin a c b
  let x := lg a b N
  let y := lg c b N
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hU := unit_positive (Γ := Γ) t
  have hPU := positive_product _ _ hP hU
  have hNU := positive_product _ _ hE hU
  have hUQ := positive_product _ _ hU hQ
  have left : Γ ⊢[PRAAx] distanceBounded (qadd g (ap2 G p x)) (qadd g (ap2 G t x)) (P+U) (P*U) :=
    sum_right_error g _ _ _ _ hPU (point_at G x p t (name_regular a b N ha))
  have right := point_at G y t q (name_regular c b N hc)
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hPU left)
  have after := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hUQ right)
  have inside := diagonal_at t a c b N W K E ha hc hW hE h
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ before inside) after
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hPU hNU) hUQ) joined
  exact le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)

/-- The unscaled log-absolute Gamma comparison retains only K/E and the two
independent original observation allowances. -/
theorem stationary_at (p q a c b N W K E : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b)
    (hW : Γ ⊢[PRAAx] le two W) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b N W) (lg a b N) K (W*E)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b) (ap2 G p (lg a b N)))) (fstT (ap2 G q (lg c b N)))
      (rateNumerator K E p q) (rateDenominator E p q) :=
  remove_upper_slack _ _ _ _ (observationCost a c b N W+two)
    (observation_slack p q (precision (fstT (qadd (margin a c b) (ap2 G p (lg a b N)))) (fstT (ap2 G q (lg c b N)))
      (rateDenominator E p q) (observationCost a c b N W+two)) a c b N W K E ha hc hW hE h)

theorem stationary_diagonal (p a c b N W K E : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b)
    (hW : Γ ⊢[PRAAx] le two W) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b N W) (lg a b N) K (W*E)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b) (ap2 G p (lg a b N)))) (fstT (ap2 G p (lg c b N)))
      (K*unit p+two*E) (E*unit p) :=
  upper_mono _ _ _ _ _ _ (denominator_positive E p p hE)
    (stationary_at p p a c b N W K E ha hc hW hE h)
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))

theorem actual_negative_interval_log_absolute_stationary_chord_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((guard (var 2) (var 4) ⋏ (guard (var 3) (var 4) ⋏ (le two (var 6) ⋏ le one (var 8)))) ⟶
        independentRate G G (centerData (var 2) (var 3) (var 4) (var 5) (var 6))
          (lg (var 2) (var 4) (var 5)) (var 7) (var 6*var 8) ⟶
        upper
          (fstT (qadd (margin (var 2) (var 3) (var 4)) (ap2 G (var 0) (lg (var 2) (var 4) (var 5)))))
          (fstT (ap2 G (var 1) (lg (var 3) (var 4) (var 5))))
          (rateNumerator (var 7) (var 8) (var 0) (var 1))
          (rateDenominator (var 8) (var 0) (var 1))) :=
  closeUniv 9 (.impI (.impI (stationary_at (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogChordStationary
