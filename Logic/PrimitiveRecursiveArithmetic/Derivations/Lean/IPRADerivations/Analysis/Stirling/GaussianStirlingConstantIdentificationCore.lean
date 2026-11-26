import IPRADerivations.Analysis.Stirling.GaussianStirlingDuplication
import IPRADerivations.Analysis.Stirling.GaussianStirlingOriginalIntegerLimit

/-!
# Cofinal comparison of the integer Stirling limit with the Stirling constant

The duplication rows are chosen at or beyond the sampling index of the
original integer limit. The half-step and residual estimates are used
at the same precision as that sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingConstantIdentificationCore

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (add_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (add_sample_error equivalent_of_envelope)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_sub_cancel)
open GaussianStirlingNames (nameData name_regular source)
open GaussianStirlingNativeDuplication (halfNumerator halfDenominator half_source double_source)
open GaussianStirlingOriginalIntegerLimit (integer_tail_contract limit_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "AF" => GaussianStirlingNames.nameF
local notation "LF" => GaussianStirlingIntegerLimit.nameF
local notation "CF" => GaussianStirlingConstant.nameF
local notation "CD" => GaussianStirlingConstant.nameData
local notation "DL" => GaussianStirlingDuplication.leftF
local notation "DR" => GaussianStirlingDuplication.rightF
local notation "LD" => GaussianStirlingDuplication.leftData
local notation "RD" => GaussianStirlingDuplication.rightData
local notation "RF" => GaussianStirlingDuplication.residualF
local notation "RX" => GaussianStirlingDuplication.residualData

/-- The needed bound on the difference of the original half-integer and integer rows. -/
def HalfStepBound (K : ℕ) : Prop :=
  ∀ {m : ℕ} {Δ : List (Fm PTm m)} (p r _ : PTm m), (Δ ⊢[PRAAx] le (num 6) (succ r)) →
    (Δ ⊢[PRAAx] distanceBounded (ap2 AF p (nameData (two*succ r+one) two))
      (ap2 AF p (nameData (succ r) one)) (num K*(unit p+succ r)) (succ r*unit p))

/-- The needed uniform bound on the named residual in the duplication identity. -/
def ResidualBound : Prop :=
  ∀ {m : ℕ} {Δ : List (Fm PTm m)} (p a b : PTm m), (Δ ⊢[PRAAx] source a b) →
    (Δ ⊢[PRAAx] distanceBounded (ap2 RF p (RX a b)) qzero
      (b*unit p+num 12*a) (num 4*a*unit p))

private def predecessor (p : PTm n) : PTm n :=
  GaussianStirlingIntegerLimit.index p+num 5

private def base (p : PTm n) : PTm n := succ (predecessor p)

private theorem base_after_index (p : PTm n) :
    Γ ⊢[PRAAx] le (GaussianStirlingIntegerLimit.index p) (base p) :=
  le_trans (le_add_right _ _) (le_succ_self _)

private theorem base_after_unit (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (base p) :=
  le_trans (GaussianStirlingIntegerLimit.index_dominates_unit p) (base_after_index p)

private theorem base_six (p : PTm n) : Γ ⊢[PRAAx] le (num 6) (base p) := by
  unfold base predecessor
  ipra_le 𝔞 (GaussianStirlingIntegerLimit.index p)

private theorem cofinal_integer (p i y : PTm n)
    (hi : Γ ⊢[PRAAx] le (GaussianStirlingIntegerLimit.index p) i) :
    Γ ⊢[PRAAx] distanceBounded (ap2 AF p (nameData i one)) (ap2 LF p y) two (unit p) := by
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have h := GaussianStirlingIntegerLimit.later_integer_distance p p i hi integer_tail_contract
  apply distance_symmetric _ _ _ _ hu
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu ?_
    (distance_congr (GaussianStirlingIntegerLimit.name_at p y).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) h)
  exact le_congr (.eqRefl _) (by ipra_ring) (le_refl _)

private theorem half_near_integer (K : ℕ) (half : HalfStepBound K) (p x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 AF p (nameData (halfNumerator (base p) one) (halfDenominator one)))
      (ap2 AF p (nameData (base p) one)) (two*num K) (unit p) := by
  let i := base p
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have hUi := base_after_unit (Γ := Γ) p
  have hi := le_trans hU hUi
  have denom : Γ ⊢[PRAAx] halfDenominator one ≐ two := by unfold halfDenominator; ipra_ring
  have h := half p (predecessor p) x (base_six (Γ := Γ) p)
  have dataEq : Γ ⊢[PRAAx] nameData (halfNumerator i one) two ≐ nameData (halfNumerator i one) (halfDenominator one) := by
    simpa only [GaussianStirlingNames.subst_nameData,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (nameData (var 0) (var 1) : PTm 2)
        (σ := ![halfNumerator i one, two]) (σ' := ![halfNumerator i one, halfDenominator one])
        (fun j => by fin_cases j; exact .eqRefl _; exact denom.eqSymm)
  have first := distance_congr (congrAp2 AF (.eqRefl p) dataEq) (.eqRefl _) (.eqRefl _) (.eqRefl _) h
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hi hU) hU ?_ first
  change Γ ⊢[PRAAx] le ((num K*(U+i))*U) ((two*num K)*(i*U))
  ipra_le (𝔞 (num K)*𝔞 U)*sl hUi

private theorem residual_near_zero (residual : ResidualBound) (p : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 RF p (RX (base p) one)) qzero (num 4) (unit p) := by
  let i := base p
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have hUi := base_after_unit (Γ := Γ) p
  have hi := le_trans hU hUi
  have hs := GaussianStirlingIntegerTail.integer_source i hi
  have hD : Γ ⊢[PRAAx] le one (num 4*i*U) :=
    positive_product _ _ (positive_product _ _ (by ipra_le 3) hi) hU
  apply distance_radius_mono _ _ _ _ _ _ hD hU ?_ (residual p i one hs)
  change Γ ⊢[PRAAx] le ((one*U+num 12*i)*U) (num 4*(num 4*i*U))
  ipra_le (𝔞 U)*sl hUi + 3*𝔞 i*𝔞 U

private def leftBudget (K : ℕ) : PTm n :=
  num 6+((GaussianNameRingLaws.three+(two+(two*num K+two)))+two)

set_option maxHeartbeats 350000 in
private theorem left_near_limit (K : ℕ) (half : HalfStepBound K) (p y x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DL p (LD (base p) one)) (ap2 LF p y) (leftBudget K) (unit p) := by
  let i := base p
  let limit := ap2 LF p y
  let X := nameData i one
  let Y := nameData (halfNumerator i one) (halfDenominator one)
  let Z := nameData (two*i) one
  let W := GaussianStirlingDuplication.leftSumData i one
  let SF := GaussianStirlingDuplication.leftSumF
  have hu := unit_positive (Γ := Γ) p
  have hi := le_trans hu (base_after_unit (Γ := Γ) p)
  have hi₂ : Γ ⊢[PRAAx] le (GaussianStirlingIntegerLimit.index p) (two*i) :=
    le_trans (base_after_index p) (by ipra_le 𝔞 i)
  have hs := GaussianStirlingIntegerTail.integer_source i hi
  have rx := name_regular i one hs
  have ry := name_regular _ _ (half_source i one hs)
  have rz := name_regular _ _ (double_source i one hs)
  have first := cofinal_integer p i y (base_after_index (Γ := Γ) p)
  have second := distance_triangle_same _ _ _ _ _ _ hu (half_near_integer K half p x) first
  have third := cofinal_integer p (two*i) y hi₂
  have sums := sum_distance _ _ _ _ _ _ _ hu first second
  have sumToLimit := distance_triangle_same _ _ _ _ _ _ hu (add_sample_error AF AF X Y p rx ry) sums
  have difference := difference_distance _ _ _ _ _ _ _ hu sumToLimit third
  have shape := GaussianNamedDifference.sample_error SF AF W Z p (add_fast _ _ _ _ rx ry) rz
  have canonical := (GaussianSignedNameExponentialOrder.real_sample_at LF y p
    (GaussianStirlingIntegerLimit.name_real (Γ := Γ) y)).andE₁
  have value := qadd_sub_cancel limit limit canonical
  exact distance_triangle_same _ _ _ _ _ _ hu shape
    (distance_congr (.eqRefl _) value (.eqRefl _) (.eqRefl _) difference)

private theorem right_near_constant (residual : ResidualBound) (p x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DR p (RD (base p) one x)) (ap2 CF p (CD x)) (num 7) (unit p) := by
  let i := base p
  let U := unit p
  let c := ap2 CF p (CD x)
  have hu := unit_positive (Γ := Γ) p
  have hs := GaussianStirlingIntegerTail.integer_source i (le_trans hu (base_after_unit p))
  have cReg := GaussianStirlingConstant.name_regular (Γ := Γ) x
  have rReg := GaussianStirlingDuplication.residual_regular i one hs
  have shape := add_sample_error CF RF (CD x) (RX i one) p cReg rReg
  have zeroError := distance_refl_zero c U hu
  have sums := sum_distance _ _ _ _ _ _ _ hu zeroError (residual_near_zero residual p)
  have can := (GaussianSignedNameExponentialOrder.real_sample_at CF (CD x) p
    (GaussianStirlingConstant.name_real (Γ := Γ) x)).andE₁
  have value := GaussianReciprocalHorner.qadd_zero_right c can
  exact distance_congr (.eqRefl _) value (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu shape sums)

def sampleBudget (K : ℕ) : PTm n := leftBudget K+(two+num 7)

theorem sample_budget_value (K : ℕ) : Γ ⊢[PRAAx] (sampleBudget K : PTm n) ≐ num (24+2*K) := by
  unfold sampleBudget leftBudget GaussianNameRingLaws.three
  apply deriveNat
  ipra_simps
  push_cast
  ring

set_option maxHeartbeats 350000 in
/-- A single comparison at precision (p) has a constant dyadic radius. -/
theorem sample_error (K : ℕ) (half : HalfStepBound K) (residual : ResidualBound) (p y x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 LF p y) (ap2 CF p (CD x)) (sampleBudget K) (unit p) := by
  let i := base p
  have hu := unit_positive (Γ := Γ) p
  have hs := GaussianStirlingIntegerTail.integer_source i (le_trans hu (base_after_unit p))
  have e := GaussianStirlingDuplication.duplication i one x hs
  have mid := diagonal_at DL DR (LD i one) (RD i one x) p (cross_to_diagonal _ _ _ _ e)
  have first := distance_symmetric _ _ _ _ hu (left_near_limit K half p y x)
  exact distance_triangle_same _ _ _ _ _ _ hu first
    (distance_triangle_same _ _ _ _ _ _ hu mid (right_near_constant residual p x))

set_option maxHeartbeats 350000 in
theorem identification (K : ℕ) (half : HalfStepBound K) (residual : ResidualBound) (y x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent LF CF y (CD x) := by
  refine equivalent_of_envelope _ _ _ _ (sampleBudget K) (limit_regular y)
    (GaussianStirlingConstant.name_regular x) (.allI ?_)
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sampleBudget,leftBudget,
    GaussianNameRingLaws.three,one,two] using
    sample_error (Γ := Γ.map Fm.shift) K half residual (var 0) (Syn.shift y) (Syn.shift x)

end LeanProofs.IPRA.Analysis.GaussianStirlingConstantIdentificationCore
