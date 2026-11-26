import IPRADerivations.Analysis.Names.GaussianNameRingLaws
import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicEntryNorm

/-!
# Actual normalized differences of regular Gaussian names

This wrapper uses the existing addition and negative-name programs.
Its literal independent operands remain visible. The regular normalized
output is within six dyadics of their actual same-query difference.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifference

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_sample_error add_sample_error)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nameF (f g : PR 2) : PR 2 := addF f (negativeF g)
def data (x y : PTm n) : PTm n := addData x (negativeData y)
ipra_subst data

theorem name_regular (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx] pointCN (nameF f g) (data x y) :=
  add_fast f (negativeF g) x (negativeData y) hf (negative_fast g y hg)

theorem negative_distance (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx] distanceBounded (qnegative a) (qnegative b) A B :=
  bound_congr (GaussianCharacteristicEntryNorm.negative_difference a b).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ hB h)

theorem difference_distance (a b c d A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) (k : Γ ⊢[PRAAx] distanceBounded c d C B) : Γ ⊢[PRAAx]
    distanceBounded (qsub a c) (qsub b d) (A+C) B :=
  sum_distance _ _ _ _ _ _ _ hB h (negative_distance _ _ _ _ hB k)

theorem sample_error (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f g) p (data x y)) (qsub (ap2 f p x) (ap2 g p y)) (num 6) (unit p) := by
  have first := add_sample_error f (negativeF g) x (negativeData y) p hf (negative_fast g y hg)
  have second := negative_sample_error g y p hg
  have trivialDistance := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ap2 f p x) (unit p) (unit_positive p)
  have joined := sum_distance _ _ _ _ _ _ _ (unit_positive p) trivialDistance second
  have endpoint : Γ ⊢[PRAAx] qadd (ap2 f p x) (qsub qzero (ap2 g p y)) ≐ qsub (ap2 f p x) (ap2 g p y) :=
    GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _))
  exact distance_congr (.eqRefl _) endpoint (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first joined)

theorem actual_regular_difference_and_raw_readback_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((pointCN f (var 0) ⋏ pointCN g (var 1)) ⟶
      pointCN (nameF f g) (data (var 0) (var 1)) ⋏
      distanceBounded (ap2 (nameF f g) (var 2) (data (var 0) (var 1)))
        (qsub (ap2 f (var 2) (var 0)) (ap2 g (var 2) (var 1))) (num 6) (unit (var 2))) :=
  closeUniv 3 (.impI (.andI (name_regular f g _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂) (sample_error f g _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedDifference
