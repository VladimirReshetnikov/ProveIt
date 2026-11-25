import IPRADerivations.Analysis.GaussianStirlingHalfStepIdentity

/-!
# Uniform bound for the original Stirling half step

The Wallis logarithm and the duplication residual yield an explicit
simultaneous bound at the literal integer and half-integer name samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingHalfStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (addF addData multiplyModulus multiply_at recode_congr sum_distance)
open GaussianNameEquivalence (cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (three add_sample_error recode_left_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul qzero qmul_canonical positive_product)
open GaussianRationalMetric (distanceBounded bounded qsub qsub_canonical)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalReconstruction (qsub_zero_right)
open GaussianRationalSyntheticDivision (qmul_congr qzero_add qzero_canonical)
open GaussianStirlingHalfStepIdentity (differenceF differenceData scaledLogF scaledLogData scaled_log_regular
  rightF rightData half_step_identity integer_source)
open GaussianStirlingNames (point nameF nameData name_regular)
open GaussianStirlingWallisGammaRatio (halfNumerator half_source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianStirlingWallisLogRate.nameF
local notation "wallData" => GaussianStirlingWallisLogRate.data
local notation "R" => GaussianStirlingDuplicationResidual.nameF
local notation "residualData" => GaussianStirlingDuplicationResidual.nameData
local notation "c" => point one two

private theorem norm_to_zero (v A B : PTm n) (hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v)
    (h : Γ ⊢[PRAAx] bounded v A B) : Γ ⊢[PRAAx] distanceBounded v qzero A B :=
  bound_congr (qsub_zero_right v hv).eqSymm (.eqRefl _) (.eqRefl _) h

private theorem lift_to_denominator (p a z w A : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] distanceBounded z w A (unit p)) :
    Γ ⊢[PRAAx] distanceBounded z w (A*a) (a*unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ ha (unit_positive p))
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) h

private theorem scaled_log_rate (p r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 scaledLogF p (scaledLogData r x)) qzero
      (num 12*unit p+num 29*succ r) (succ r*unit p) := by
  let a := succ r
  let d := wallData r x
  let q := GaussianFastValueCut.exponent (multiplyModulus constantF H c d) p
  let u := ap2 H q d
  let V := unit q
  let U := unit p
  have hD := positive_product (Γ := Γ) a U (zero_lt_succ r) (unit_positive p)
  have hE := positive_product (Γ := Γ) a V (zero_lt_succ r) (unit_positive q)
  have hc : Γ ⊢[PRAAx] bounded c one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one (le_succ_self one)
      (le_congr (.eqRefl _) (one_mul two).eqSymm (le_succ_self one))
  have hu := (GaussianSignedNameExponentialOrder.real_sample_at (Γ := Γ) H d q (GaussianStirlingWallisLogRate.name_real r x)).andE₁
  have logBound : Γ ⊢[PRAAx] bounded u (num 12*V+num 29*a) (a*V) :=
    bound_congr (qsub_zero_right u hu) (.eqRefl _) (.eqRefl _) (GaussianStirlingWallisLogRate.ratio_log_rate q r x hn)
  have product := bounded_product c u one one (num 12*V+num 29*a) (a*V) (le_refl one) hE hc logBound
  have atClock : Γ ⊢[PRAAx] distanceBounded (qmul c u) qzero (num 12*V+num 29*a) (a*V) :=
    norm_to_zero _ _ _ (qmul_canonical _ _)
      (bound_congr (.eqRefl _) (one_mul _) (one_mul _) product)
  have read : Γ ⊢[PRAAx] ap2 scaledLogF p (scaledLogData r x) ≐ GaussianFastValueCut.recode (qmul c u) :=
    (multiply_at constantF H c d p).eqTrans (recode_congr (qmul_congr (constant_at q c) (.eqRefl _)))
  have clocks : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right p _)
  have close : Γ ⊢[PRAAx] le ((num 12*V+num 29*a)*(a*U)) ((num 12*U+num 29*a)*(a*V)) := by
    let 𝔞 := fun t : PTm n => Groth.ι (IPRA.Q.mk Γ t)
    ipra_le 29*(𝔞 a)^2*sl clocks
  exact distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hE hD close (recode_left_distance _ _ _ _ hE atClock))

private theorem residual_rate (p r : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (residualData (succ r) one)) qzero
      (unit p+num 3*succ r) (succ r*unit p) := by
  let a := succ r
  let u := unit p
  have ha := zero_lt_succ (Γ := Γ) r
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ ha hu
  have hE : Γ ⊢[PRAAx] le one (num 4*a*u) :=
    positive_product _ _ (positive_product _ _ (by ipra_le 3) ha) hu
  have rate := GaussianStirlingDuplicationResidual.uniform_sample_bound p a one (integer_source (Γ := Γ) r)
  refine distance_radius_mono _ _ _ _ _ _ hE hD ?_ rate
  change Γ ⊢[PRAAx] le ((one*u+num 12*a)*(a*u)) ((u+num 3*a)*(num 4*a*u))
  exact le_congr (.eqRefl _) (by ipra_ring) (le_add_right _ (num 3*a*(u*u)))

private theorem rhs_rate (p r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rightF p (rightData r x)) qzero (num 13*unit p+num 35*succ r) (succ r*unit p) := by
  let a := succ r
  let y := scaledLogData r x
  let z := residualData a one
  have ha := zero_lt_succ (Γ := Γ) r
  have hD := positive_product _ _ ha (unit_positive p)
  have rs := GaussianStirlingDuplicationResidual.name_regular a one (integer_source (Γ := Γ) r)
  have first := lift_to_denominator p a _ _ three ha (add_sample_error scaledLogF R y z p (scaled_log_regular r x hn) rs)
  have last := sum_distance _ _ _ _ _ _ _ hD (scaled_log_rate p r x hn) (residual_rate p r)
  exact distance_congr (.eqRefl _) (qzero_add qzero qzero_canonical)
    (by dsimp only [three,a]; ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hD first last)

theorem half_step_error (p r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData (two*succ r+one) two)) (ap2 nameF p (nameData (succ r) one))
      (num 64*(unit p+succ r)) (succ r*unit p) := by
  let a := succ r
  let b := halfNumerator r
  let M := ap2 nameF p (nameData b two)
  let N := ap2 nameF p (nameData a one)
  have ha := zero_lt_succ (Γ := Γ) r
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ ha hu
  have circ := half_step_identity r x hn
  have e0 := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ circ)
  have first := GaussianNamedDifference.sample_error nameF nameF (nameData b two) (nameData a one) p
    (name_regular _ _ (half_source (Γ := Γ) r)) (name_regular _ _ (integer_source r))
  have leg := lift_to_denominator p a _ _ (num 6) ha (distance_symmetric _ _ _ _ hu first)
  have mid := lift_to_denominator p a _ _ two ha e0
  have join := distance_triangle_same _ _ _ _ _ _ hD leg
    (distance_triangle_same _ _ _ _ _ _ hD mid (rhs_rate p r x hn))
  have centered : Γ ⊢[PRAAx] distanceBounded (qsub M N) qzero (num 13*unit p+num 43*a) (a*unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [a]; ipra_ring) (.eqRefl _) join
  have final := distance_radius_mono _ _ _ _ (num 64*(unit p+a)) _ hD hD
    (le_congr (.eqRefl _) (by dsimp only [a]; ipra_ring)
      (le_add_right _ ((num 51*unit p+num 21*a)*(a*unit p)))) centered
  exact bound_congr (qsub_zero_right (qsub M N) (qsub_canonical M N)) (.eqRefl _) (.eqRefl _) final

theorem actual_stirling_half_step_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (num 6) (succ (var 1)) ⟶
      distanceBounded (ap2 nameF (var 0) (nameData (two*succ (var 1)+one) two))
        (ap2 nameF (var 0) (nameData (succ (var 1)) one))
        (num 64*(unit (var 0)+succ (var 1))) (succ (var 1)*unit (var 0))) :=
  closeUniv 3 (.impI (half_step_error (var 0) (var 1) (var 2) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingHalfStep
