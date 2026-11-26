import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorCoefficientCauchy
import IPRADerivations.Analysis.Names.GaussianFastValueCut

/-!
# A common modulus for the retained original Barnes exponent coefficients

The sharper low- and high-degree estimates combine into a uniform
coefficient estimate at any fixed retained order. The actual buffers
may be built with separate prefactor clocks, cutoffs and retained orders.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorRetainedCoefficient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer)
open GaussianBarnesCanonicalExponentTaylorCoefficientCauchy
  (stored cutoffNumerator cutoffDenominator clockNumerator clockDenominator gapNumerator gapDenominator
    linearGain cutoff_denominator_positive constant_entry_gap linear_entry_gap quadratic_entry_gap higher_entry_gap)
open GaussianBarnesCanonicalHigherRows (previous degree coefficientGain)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefactorLipschitz (halfGain)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D₁" => GaussianBarnesCanonicalDerivativeRow.boundNumerator
local notation "D₂" => GaussianBarnesCanonicalSecondDerivativeRow.boundNumerator
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def tailGain (R M : PTm n) : PTm n := D₁ R+D₂ R+pw two (previous M)
def prefactorGain (R : PTm n) : PTm n := linearGain R+halfGain

def cutoff (p R M : PTm n) : PTm n := tailGain R M*unit p
def precision (p R : PTm n) : PTm n := exponent (prefactorGain R) p

theorem gap_denominator_positive (q t R r s : PTm n) : Γ ⊢[PRAAx] le one (gapDenominator q t R r s) :=
  positive_product _ _ (positive_product _ _ (unit_positive q) (unit_positive t))
    (cutoff_denominator_positive R r s)

private theorem tail_gain_first (R M : PTm n) : Γ ⊢[PRAAx] le (D₁ R) (tailGain R M) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

private theorem tail_gain_second (R M : PTm n) : Γ ⊢[PRAAx] le (D₂ R) (tailGain R M) :=
  le_trans (le_add_left _ _) (le_add_right _ _)

private theorem increase (x y q t R r s A K A' K' : PTm n)
    (ha : Γ ⊢[PRAAx] le A A') (hk : Γ ⊢[PRAAx] le K K')
    (h : Γ ⊢[PRAAx] distanceBounded x y (gapNumerator q t R r s A K) (gapDenominator q t R r s)) :
    Γ ⊢[PRAAx] distanceBounded x y (gapNumerator q t R r s A' K') (gapDenominator q t R r s) := by
  let E := gapDenominator q t R r s
  have hE := gap_denominator_positive (Γ := Γ) q t R r s
  apply distance_radius_mono _ _ _ _ _ _ hE hE _ h
  unfold gapNumerator clockNumerator cutoffNumerator
  ipra_le 𝔞 E*𝔞 (cutoffDenominator R r s)*(𝔞 (unit q)+𝔞 (unit t))*sl hk+
    𝔞 E*𝔞 (clockDenominator q t)*(𝔞 (initial R+r)+𝔞 (initial R+s))*sl ha

private theorem with_clocks (x y q t R r s A K : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (cutoffNumerator R r s A) (cutoffDenominator R r s)) :
    Γ ⊢[PRAAx] distanceBounded x y (gapNumerator q t R r s A K) (gapDenominator q t R r s) :=
  distance_radius_mono _ _ _ _ _ _ (cutoff_denominator_positive R r s) (gap_denominator_positive q t R r s)
    (le_of_eq_add (d := clockNumerator q t K*cutoffDenominator R r s*cutoffDenominator R r s)
      (by unfold gapNumerator gapDenominator; ipra_ring)) h

private theorem stored_congr (q z R B r M : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] stored q z R B r M a ≐ stored q z R B r M b :=
  entry_congr (.eqRefl (buffer q z R B r M)) (congrMonus (.eqRefl (previous M)) h)

private theorem transport_index (q t z R B r s M L e f P D : PTm n) (h : Γ ⊢[PRAAx] e ≐ f)
    (hg : Γ ⊢[PRAAx] distanceBounded (stored q z R B r M f) (stored t z R B s L f) P D) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M e) (stored t z R B s L e) P D :=
  distance_congr (stored_congr q z R B r M h).eqSymm (stored_congr t z R B s L h).eqSymm (.eqRefl _) (.eqRefl _) hg

theorem entry_gap (q t z R B r s M L e : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hm : Γ ⊢[PRAAx] le e (previous M)) (hl : Γ ⊢[PRAAx] le e (previous L)) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M e) (stored t z R B s L e)
      (gapNumerator q t R r s (tailGain R M) (prefactorGain R)) (gapDenominator q t R r s) := by
  refine .orE (lt_or_le e one) ?_ ?_
  · have eq : lt e one :: Γ ⊢[PRAAx] e ≐ zero :=
      le_antisymm ((succ_monus_succ e zero).eqSymm.eqTrans Prf.hyp0) (zero_le e)
    have raw := constant_entry_gap (Γ := lt e one :: Γ) q t z R B r s M L
    have room : lt e one :: Γ ⊢[PRAAx] le
        (zero*gapDenominator q t R r s) (gapNumerator q t R r s (tailGain R M) (prefactorGain R)*one) :=
      le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _)
    exact transport_index q t z R B r s M L e zero _ _ eq
      (distance_radius_mono _ _ _ _ _ _ (le_refl one) (gap_denominator_positive q t R r s) room raw)
  · refine .orE (lt_or_le e two) ?_ ?_
    · have eq : lt e two :: le one e :: Γ ⊢[PRAAx] e ≐ one :=
        le_antisymm ((succ_monus_succ e one).eqSymm.eqTrans Prf.hyp0) Prf.hyp1
      exact transport_index q t z R B r s M L e one _ _ eq (increase _ _ q t R r s _ _ _ _
        (tail_gain_first R M) (le_add_right _ _) (linear_entry_gap q t z R B r s M L h.wk.wk))
    · refine .orE (lt_or_le e (num 3)) ?_ ?_
      · have eq : lt e (num 3) :: le two e :: le one e :: Γ ⊢[PRAAx] e ≐ two :=
          le_antisymm ((succ_monus_succ e two).eqSymm.eqTrans Prf.hyp0) Prf.hyp1
        exact transport_index q t z R B r s M L e two _ _ eq (increase _ _ q t R r s _ _ _ _
          (tail_gain_second R M) (le_add_left _ _) (quadratic_entry_gap q t z R B r s M L h.wk.wk.wk))
      · let Δ := le (num 3) e :: le two e :: le one e :: Γ
        let j := monus e (num 3)
        have add := eq_add_of_le (Prf.hyp0 : Δ ⊢[PRAAx] le (num 3) e)
        have eq : Δ ⊢[PRAAx] e ≐ degree j :=
          add.eqTrans (by unfold degree previous j; ipra_ring)
        have hm' : Δ ⊢[PRAAx] le (degree j) (previous M) :=
          le_congr eq (.eqRefl _) hm.wk.wk.wk
        have hl' : Δ ⊢[PRAAx] le (degree j) (previous L) :=
          le_congr eq (.eqRefl _) hl.wk.wk.wk
        have small : Δ ⊢[PRAAx] le (coefficientGain j) (tailGain R M) :=
          le_trans (GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) hm') (le_add_left _ _)
        have near := higher_entry_gap q t z R B j r s M L h.wk.wk.wk hm' hl'
        have pay := mul_le_mul_right (cutoffDenominator R r s)
          (add_le_add₂ (mul_le_mul_right (initial R+s) small) (mul_le_mul_right (initial R+r) small))
        exact transport_index q t z R B r s M L e (degree j) _ _ eq
          (with_clocks _ _ q t R r s (tailGain R M) (prefactorGain R)
            (distance_radius_mono _ _ _ _ _ _ (cutoff_denominator_positive R r s) (cutoff_denominator_positive R r s)
              pay near))

theorem late_entry_gap (p q t z R B r s M L e : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hm : Γ ⊢[PRAAx] le e (previous M)) (hl : Γ ⊢[PRAAx] le e (previous L))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M e) (stored t z R B s L e) (num 4) (unit p) := by
  let E := cutoffDenominator R r s
  let V := clockDenominator q t
  have ar : Γ ⊢[PRAAx] le (tailGain R M*unit p) (initial R+r) := le_trans hr (le_add_left _ _)
  have as : Γ ⊢[PRAAx] le (tailGain R M*unit p) (initial R+s) := le_trans hs (le_add_left _ _)
  refine distance_radius_mono _ _ _ _ _ _ (gap_denominator_positive q t R r s) (unit_positive p) ?_
    (entry_gap q t z R B r s M L e h hm hl)
  unfold gapNumerator gapDenominator clockNumerator cutoffNumerator
  ipra_le 𝔞 (unit t)*𝔞 E*sl hq+𝔞 (unit q)*𝔞 E*sl ht+
    𝔞 (initial R+s)*𝔞 V*sl ar+𝔞 (initial R+r)*𝔞 V*sl as using
      dsimp only [E,V,cutoffDenominator,clockDenominator]
      ipra_simps
      ring

theorem scheduled_entry_gap (p t z R B s M L e : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hm : Γ ⊢[PRAAx] le e (previous M)) (hl : Γ ⊢[PRAAx] le e (previous L))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] distanceBounded (stored (precision p R) z R B (cutoff p R M) M e)
      (stored t z R B s L e) (num 4) (unit p) :=
  late_entry_gap p _ t z R B _ s M L e h hm hl (query_budget _ _) ht (le_refl _) hs

theorem actual_Barnes_retained_exponent_coefficient_Cauchy_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let p := var 0
     let q := var 1
     let t := var 2
     let z := var 3
     let R := var 4
     let B := var 5
     let r := var 6
     let s := var 7
     let M := var 8
     let L := var 9
     let e := var 10
     (source z R B ⋏ (le e (previous M) ⋏ le e (previous L))) ⟶
       ((le (prefactorGain R*unit p) (unit q) ⋏ le (prefactorGain R*unit p) (unit t)) ⋏
         (le (cutoff p R M) r ⋏ le (cutoff p R M) s)) ⟶
       distanceBounded (stored q z R B r M e) (stored t z R B s L e) (num 4) (unit p)) :=
  closeUniv 11 (.impI (.impI (late_entry_gap _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorRetainedCoefficient
