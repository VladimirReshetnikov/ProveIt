import IPRADerivations.Analysis.GaussianRightHalfPlaneArgumentLocalBound
import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithm
import IPRADerivations.Analysis.GaussianPositiveRationalLogarithmVariation
import IPRADerivations.Analysis.GaussianBetaUpperPowerCancellation

/-!
# A uniform late-observation bound near one

The rectangular enclosure of the one-eighth disk bounds the squared
modulus between 49/64 and 82/64. The original real logarithm's variation
from the exact zero sample at one bounds the radial logarithm after
eight bits. The original signed argument is bounded by 1/7 at every
precision. Their actual sum has norm at most 1/2 at all late precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmLocalBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale normSq normSq_one normSq_scale)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianPositiveRationalLogarithm (logF sample sample_canonical)
open GaussianRationalHorner (qzero qmul ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalHarmonicIntervalVariation (gap)
open RationalValueBounds (positive_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "H" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "G" => GaussianRightHalfPlaneArgument.nameF
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "Xd" => GaussianRightHalfPlaneRadialLogarithm.data
local notation "Yd" => GaussianRightHalfPlaneArgument.data
local notation "Zd" => GaussianRightHalfPlaneLogarithm.data
local notation "R" => GaussianPositiveRationalLogarithm.data
local notation "hpt" => GaussianEulerSquareFactorInverse.half

def box (A B D : PTm n) : Fm PTm n :=
  le one A ⋏ (le one D ⋏
    (le (num 7*D) (num 8*A) ⋏ (le (num 8*A) (num 9*D) ⋏ le (num 8*B) D)))

private theorem eight_positive : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
private theorem sixty_four_positive : Γ ⊢[PRAAx] le one (num 64 : PTm n) := by ipra_le 63

theorem phase_guard (A B D : PTm n) (h : Γ ⊢[PRAAx] box A B D) :
    Γ ⊢[PRAAx] le (num 7*B) A := by
  apply positive_cancel (c := num 8) eight_positive
  exact le_congr (by ipra_ring) (.eqRefl _)
    (le_trans (le_mul_mono (le_refl (num 7)) h.andE₂.andE₂.andE₂.andE₂) h.andE₂.andE₂.andE₁)

theorem norm_box (A B D : PTm n) (h : Γ ⊢[PRAAx] box A B D) :
    Γ ⊢[PRAAx] le (num 49*normDen D) (num 64*normNum A B) ⋏
      le (num 64*normNum A B) (num 82*normDen D) := by
  have h₁ := h.andE₂.andE₂.andE₁
  have h₂ := h.andE₂.andE₂.andE₂.andE₁
  have h₃ := h.andE₂.andE₂.andE₂.andE₂
  have a : Γ ⊢[PRAAx] le (num 49*(D*D)) (num 64*(A*A)) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono h₁ h₁)
  have b : Γ ⊢[PRAAx] le (num 64*(A*A)) (num 81*(D*D)) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono h₂ h₂)
  have r : Γ ⊢[PRAAx] le (num 64*(B*B)) (D*D) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono h₃ h₃)
  refine .andI ?_ ?_
  · apply le_trans a
    unfold normNum
    ipra_le 64*𝔞 (B*B)
  · exact le_congr (by unfold normNum; ipra_ring) (by unfold normDen; ipra_ring)
      (Foundations.FiniteHausdorff.sum_mono b r)

private theorem half_floor (A B D : PTm n) (h : Γ ⊢[PRAAx] box A B D) :
    Γ ⊢[PRAAx] le (normDen D) (two*normNum A B) := by
  have pos : Γ ⊢[PRAAx] le one (num 32 : PTm n) := by ipra_le 31
  have initial : Γ ⊢[PRAAx] le (num 32*normDen D) (num 49*normDen D) := by
    ipra_le 17*𝔞 (normDen D)
  have result := le_trans initial (norm_box A B D h).andE₁
  exact positive_cancel pos (le_congr (.eqRefl _) (by ipra_ring) result)

private theorem norm_gap (A B D : PTm n) (h : Γ ⊢[PRAAx] box A B D) :
    Γ ⊢[PRAAx] le (num 64*gap (normNum A B) (normDen D) one one) (num 18*normDen D*one) := by
  let N := normNum A B
  let Q := normDen D
  have forward : Γ ⊢[PRAAx] le (num 64*N) (num 64*Q+num 18*Q) :=
    le_congr (.eqRefl _) (by ipra_ring) (norm_box A B D h).andE₂
  have lower : Γ ⊢[PRAAx] le (num 49*Q) (num 64*N) := (norm_box A B D h).andE₁
  have reverse : Γ ⊢[PRAAx] le (num 64*Q) (num 64*N+num 18*Q) := by
    ipra_le sl lower+3*𝔞 Q
  have both := LeanProofs.IPRA.Probability.MedianWeighted.ad_le_of forward reverse
  have gap_eq : Γ ⊢[PRAAx] gap N Q one one ≐ Probability.Variance.ad N Q := by
    unfold gap Probability.Variance.ad
    exact congrAdd (congrMonus (by ipra_ring) (by ipra_ring)) (congrMonus (by ipra_ring) (by ipra_ring))
  exact le_congr ((LeanProofs.IPRA.Probability.MedianWeighted.ad_mul (num 64) N Q).eqTrans (congrMul (.eqRefl _) gap_eq.eqSymm))
    (by ipra_ring) both

private theorem unit_late (p : PTm n) (h : Γ ⊢[PRAAx] le (num 8) p) :
    Γ ⊢[PRAAx] le (num 256) (unit p) := by
  have k : Γ ⊢[PRAAx] num 16*num 16 ≐ num 256 := by ipra_ring
  have e : Γ ⊢[PRAAx] unit (num 8) ≐ num 256 := by
    unfold unit
    exact (Combinatorics.BinomialTheorem.congrPw (.eqRefl two) (by ipra_ring : Γ ⊢[PRAAx] num 8 ≐ num 4+num 4)).eqTrans
      ((pw_add two (num 4) (num 4)).eqTrans
        ((congrMul GaussianFiniteLogarithmDyadicTail.two_four GaussianFiniteLogarithmDyadicTail.two_four).eqTrans k))
  exact le_congr e (.eqRefl _) (GaussianExponentialReference.unit_monotone h)

private theorem log_one (p : PTm n) : Γ ⊢[PRAAx] sample p one one ≐ qzero :=
  (GaussianBetaUpperPowerCancellation.rational_log_integer_at p one).eqTrans
    (GaussianBetaUpperPowerCancellation.integer_log_at_one (GaussianBetaUpperPowerCancellation.logClock p))

theorem squared_radius_log_bound (p A B D : PTm n) (hx : Γ ⊢[PRAAx] box A B D)
    (hp : Γ ⊢[PRAAx] le (num 8) p) :
    Γ ⊢[PRAAx] bounded (sample p (normNum A B) (normDen D)) two (num 3) := by
  let a := normNum A B
  let b := normDen D
  let U := unit p
  let q := sample p a b
  have hs := GaussianRightHalfPlaneRadialLogarithm.log_source A B D hx.andE₁ hx.andE₂.andE₁
  have dist := GaussianPositiveRationalLogarithmVariation.diagonal_native p a b one one two (num 18) (num 64)
    hs (.andI (le_refl _) (le_refl _)) sixty_four_positive (half_floor A B D hx)
    (le_congr (.eqRefl _) (by ipra_ring) (le_succ_self one)) (norm_gap A B D hx)
  have eq : Γ ⊢[PRAAx] GaussianRationalMetric.qsub q (sample p one one) ≐ q :=
    (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl q) (log_one p)).eqTrans
    (GaussianRationalReconstruction.qsub_zero_right _ (sample_canonical p a b))
  have high := unit_late p hp
  have budget : Γ ⊢[PRAAx] le
      (((two*num 18)*U+num 17*num 64)*num 3) (two*(num 64*U)) := by
    ipra_le 20*sl high+1856
  have three : Γ ⊢[PRAAx] le one (num 3 : PTm n) := by ipra_le 2
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ sixty_four_positive (unit_positive p)) three budget
    (bound_congr eq (.eqRefl _) (.eqRefl _) dist)

private theorem half_bound : Γ ⊢[PRAAx] bounded (hpt : PTm n) one two := by
  let z : PTm n := scale one oneCode
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hn : Γ ⊢[PRAAx] normSq z ≐ one :=
    (normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  apply bounded_of_cleared _ z two one two ht ht (ofGaussian_represents z two ht)
  exact le_congr
    ((by ipra_ring : Γ ⊢[PRAAx] two*two ≐ (two*two)*one).eqTrans (congrMul (.eqRefl _) hn.eqSymm))
    (by ipra_ring) (le_refl (two*two))

theorem radial_bound (p A B D : PTm n) (hx : Γ ⊢[PRAAx] box A B D) (hp : Γ ⊢[PRAAx] le (num 8) p) :
    Γ ⊢[PRAAx] bounded (ap2 H p (Xd A B D)) one (num 3) := by
  let y := R (normNum A B) (normDen D)
  let j := GaussianNamedBoundedProductObservation.clock constantF logF p hpt y
  have e := (GaussianNamedBoundedProductObservation.name_at (Γ := Γ) constantF logF p hpt y).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (constant_at j hpt) (.eqRefl _))
  have late : Γ ⊢[PRAAx] le (num 8) j := le_trans hp (le_add_right _ _)
  have three : Γ ⊢[PRAAx] le one (num 3 : PTm n) := by ipra_le 2
  have tp : Γ ⊢[PRAAx] le one two := le_succ_self one
  have m := bounded_product hpt (ap2 logF j y) one two two (num 3) tp three half_bound
    (squared_radius_log_bound j A B D hx late)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ tp three) three
    (le_of_eq_add (d := zero) (by ipra_ring)) (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) m)

theorem sample_bound (p A B D neg : PTm n) (hx : Γ ⊢[PRAAx] box A B D)
    (hs : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) (hp : Γ ⊢[PRAAx] le (num 8) p) :
    Γ ⊢[PRAAx] bounded (ap2 L p (Zd A B D neg)) one two := by
  let j := GaussianFastValueCut.exponent two p
  let x := Xd A B D
  let y := Yd A B neg
  have late : Γ ⊢[PRAAx] le (num 8) j := le_trans hp (le_add_right _ _)
  have rad := radial_bound j A B D hx late
  have phase := GaussianRightHalfPlaneArgumentLocalBound.one_seventh j A B neg hx.andE₁ (phase_guard A B D hx) hs
  have three : Γ ⊢[PRAAx] le one (num 3 : PTm n) := by ipra_le 2
  have seven : Γ ⊢[PRAAx] le one (num 7 : PTm n) := by ipra_le 6
  have m := bounded_sum (ap2 H j x) (ap2 G j y) one (num 3) one (num 7) three seven rad phase
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ three seven) (le_succ_self one)
    (by ipra_le 1)
    (bound_congr (GaussianExponentialReference.add_sample H G x y p).eqSymm (.eqRefl _) (.eqRefl _) m)

theorem actual_right_half_plane_logarithm_late_half_disk_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((box (var 0) (var 1) (var 2) ⋏ (((var 3 ≐ zero) ⋎ (var 3 ≐ one)) ⋏ le (num 8) (var 4))) ⟶
        bounded (ap2 L (var 4) (Zd (var 0) (var 1) (var 2) (var 3))) one two) :=
  closeUniv 5 (.impI (sample_bound _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmLocalBound
