import IPRADerivations.Analysis.GaussianArctangentDivisionAngles
import IPRADerivations.Analysis.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.GaussianNamedSineFromExponential

/-!
# Literal divided angles give zeros at the original multiple angle

At their actual independent clocks the integer-scaled divided angle
and the scaled half turn both multiply the original quarter turn by
2k. This identifies the exponential with the actual k-th power of
minus one, whose inverse is itself, and gives sine zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngleRoots

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentDivisionAngles (source coefficient modulus odd_source)
open GaussianArctangentExponentialPeriod (twiceF twiceData twiceRadius minusOne minusOneCode negative_one_square)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNamedSineFromExponential (sineF sineData sine_constant negative_exponential_constant)
open GaussianNameEquivalence (point_at crossEquivalent cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul qadd qzero positive_product ofGaussian_represents ofGaussian_canonical
  qmul_canonical qmul_represents canonical_unique represents_rescale represents_congr)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalNaturalScale (natScale naturalPoint natural_point_represents natural_product_value
  natScale_as_product natScale_congr natScale_add)
open GaussianRationalReciprocal (qone power powerF)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal_refl)
open GaussianExponentialReference (add_input unit_monotone)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def multipleF : PR 2 := GaussianNamedNaturalScale.nameF GaussianArctangentDivisionAngles.nameF
def multipleData (k m z : PTm n) : PTm n :=
  GaussianNamedNaturalScale.data m m (GaussianArctangentDivisionAngles.data k m z)
def multipleRadius (m : PTm n) : PTm n := GaussianNamedNaturalScale.radius m two
def halfPowerF : PR 2 := GaussianNamedNaturalScale.nameF twiceF
def halfPowerData (k z : PTm n) : PTm n := GaussianNamedNaturalScale.data k k (twiceData z)
def halfPowerRadius (k : PTm n) : PTm n := GaussianNamedNaturalScale.radius k twiceRadius

@[simp] theorem subst_multipleData {l : ℕ} (σ : Fin n → PTm l) (k m z : PTm n) :
    Syn.subst σ (multipleData k m z) = multipleData (Syn.subst σ k) (Syn.subst σ m) (Syn.subst σ z) :=
  by simp [multipleData]

@[simp] theorem subst_halfPowerData {l : ℕ} (σ : Fin n → PTm l) (k z : PTm n) :
    Syn.subst σ (halfPowerData k z) = halfPowerData (Syn.subst σ k) (Syn.subst σ z) :=
  by simp [halfPowerData,twiceData]

theorem multiple_input (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input multipleF (multipleRadius m) (multipleData k m z) :=
  GaussianNamedNaturalScale.exponential_input _ _ _ _ _ (GaussianArctangentDivisionAngles.exponential_input k m z h)
    (le_refl m)

private theorem quarter_input (z : PTm n) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input quarterF two z :=
  GaussianArctangentQuarterExponential.quarter_input z (GaussianArctangentQuarterExponential.original_bounded_arguments z)

private theorem half_input (z : PTm n) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input twiceF twiceRadius (twiceData z) :=
  add_input quarterF quarterF two z z (quarter_input z) (quarter_input z)

private theorem half_power_input (k z : PTm n) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input halfPowerF (halfPowerRadius k) (halfPowerData k z) :=
  GaussianNamedNaturalScale.exponential_input _ _ _ _ _ (half_input z) (le_refl k)

private theorem clear_coefficient (k m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (naturalPoint m) (coefficient k m) ≐ naturalPoint (two*k) := by
  let a := scale (two*k) oneCode
  have left := qmul_represents (naturalPoint m) (coefficient k m) (scale m oneCode) a one m (le_refl one) hm
    (natural_point_represents m) (ofGaussian_represents _ _ hm)
  have right := represents_rescale (naturalPoint (two*k)) a one m (natural_point_represents (Γ := Γ) (two*k))
  exact canonical_unique _ _ _ m (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) hm
    (represents_congr (.eqRefl _) (natural_product_value m a) (one_mul m) left)
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul m) right)

private theorem scaled_coefficient (k m q : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] natScale m (qmul (coefficient k m) q) ≐ natScale (two*k) q :=
  (natScale_as_product _ _).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (clear_coefficient k m hm) (.eqRefl _)).eqTrans (natScale_as_product _ _).eqSymm))

private theorem scaled_double (k q : PTm n) :
    Γ ⊢[PRAAx] natScale k (qadd q q) ≐ natScale (two*k) q :=
  (natScale_as_product _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (natScale_as_product _ _).eqSymm (natScale_as_product _ _).eqSymm).eqTrans
        ((natScale_add k k q).eqSymm.eqTrans (natScale_congr (by ipra_ring) (.eqRefl _)))))

private def leftClock (p m : PTm n) : PTm n := GaussianArctangentDivisionAngles.clock (GaussianNamedNaturalScale.clock p m)
private def rightClock (p k : PTm n) : PTm n := GaussianFastValueCut.exponent two (GaussianNamedNaturalScale.clock p k)

private theorem multiple_at (p k m z : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 multipleF p (multipleData k m z) ≐ natScale (two*k) (ap2 quarterF (leftClock p m) z) :=
  (GaussianNamedNaturalScale.sample_at _ p m m _).eqTrans
    ((natScale_congr (.eqRefl _) (GaussianArctangentDivisionAngles.sample_at k m z _)).eqTrans
      (scaled_coefficient _ _ _ hm))

private theorem half_power_at (p k z : PTm n) :
    Γ ⊢[PRAAx] ap2 halfPowerF p (halfPowerData k z) ≐ natScale (two*k) (ap2 quarterF (rightClock p k) z) :=
  (GaussianNamedNaturalScale.sample_at _ p k k _).eqTrans
    ((natScale_congr (.eqRefl _) (GaussianExponentialReference.add_sample quarterF quarterF z z _)).eqTrans
      (scaled_double _ _))

private theorem multiple_distance (p k m z : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 multipleF p (multipleData k m z)) (ap2 halfPowerF p (halfPowerData k z))
      (num 4*k) (unit p) := by
  let s := leftClock p m
  let t := rightClock p k
  let P := unit p
  let S := unit s
  let T := unit t
  have hs : Γ ⊢[PRAAx] le P S := unit_monotone
    (le_trans (GaussianNamedNaturalScale.clock_later p m) (le_add_right _ _))
  have ht : Γ ⊢[PRAAx] le P T := unit_monotone
    (le_trans (GaussianNamedNaturalScale.clock_later p k) (le_add_right _ _))
  have den := positive_product _ _ (unit_positive (Γ := Γ) s) (unit_positive t)
  have hbound := GaussianRadiusExponentialName.bounded_samples_at _ _ _ t (quarter_input (Γ := Γ) z).andE₂
  have diff := GaussianNamedNaturalScale.scaled_distance (two*k) _ _ _ _ two den
    (point_at quarterF z s t (quarter_regular z)) hbound
  have cost : Γ ⊢[PRAAx] le ((two*k*(S+T))*P) ((num 4*k)*(S*T)) :=
    by ipra_le 𝔞 (two*k)*𝔞 T*sl hs+𝔞 (two*k)*𝔞 S*sl ht
  exact distance_congr (multiple_at p k m z hm).eqSymm (half_power_at p k z).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ den (unit_positive p) cost diff)

theorem multiple_half_power_cross (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] crossEquivalent multipleF halfPowerF (multipleData k m z) (halfPowerData k z) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (num 4*k)
    (multiple_input k m z h).andE₁ (half_power_input k z).andE₁
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using h.andE₁.shift
  simpa only [GaussianNamedDiagonalRate.diagonalRate,Syn.shift,subst_multipleData,subst_halfPowerData,
    PTm.subst_mul,PTm.subst_num] using multiple_distance (var 0) (Syn.shift k) (Syn.shift m) (Syn.shift z) hs

private theorem negative_one_bound : Γ ⊢[PRAAx] bounded (minusOne : PTm n) one one := by
  have e : Γ ⊢[PRAAx] normSq (minusOneCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [minusOneCode,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact bounded_of_cleared _ _ _ _ _ (le_refl one) (le_refl one) (ofGaussian_represents _ _ (le_refl one))
    (le_congr (e.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_refl one))

theorem multiple_exponential (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF multipleF) constantF
      (GaussianRadiusExponentialName.data (multipleRadius m) (multipleData k m z)) (power minusOne k) := by
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (multiple_input k m z h) (half_power_input k z) (multiple_half_power_cross k m z h)
  exact cross_trans _ _ _ _ _ _ exp
    (GaussianBoundedIntegerExponential.integer_power_cross twiceF k twiceRadius (twiceData z) minusOne one
      (.andI (half_input z) (.andI (GaussianArctangentOriginalExponential.half_turn_cross z) negative_one_bound)))

private theorem half_power_square (k : PTm n) : Γ ⊢[PRAAx] qmul (power minusOne k) (power minusOne k) ≐ qone :=
  (GaussianRationalPowerAlgebra.power_product minusOne minusOne k).eqSymm.eqTrans
    ((congrAp2 powerF (.eqRefl k) negative_one_square).eqTrans (GaussianRationalRoundedPower.qone_power k))

theorem multiple_sine_zero (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] crossEquivalent (sineF multipleF) constantF (sineData multipleF (multipleRadius m) (multipleData k m z)) qzero := by
  have hi := multiple_input k m z h
  have exp := multiple_exponential k m z h
  have negExp := negative_exponential_constant _ _ _ _ _ hi exp (half_power_square k)
  have zero : Γ ⊢[PRAAx] qmul GaussianNamedSineFromExponential.multiplier (qsub (power minusOne k) (power minusOne k))
      ≐ qzero :=
    (qmul_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
  exact cross_trans _ _ _ _ _ _ (sine_constant _ _ _ _ _ hi exp negExp) (constant_data_cross _ _ zero)

theorem actual_odd_division_angle_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ crossEquivalent (sineF multipleF) constantF
      (sineData multipleF (multipleRadius (modulus (var 1))) (multipleData (var 0) (modulus (var 1)) (var 2))) qzero) :=
  closeUniv 3 (.impI (multiple_sine_zero _ _ _ (odd_source _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngleRoots
