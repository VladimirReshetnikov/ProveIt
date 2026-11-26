import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalCorrectionSlope
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalEndpoints
import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaLipschitz

/-!
# Upper slope of the shifted digamma on the truncated negative interval

The positive digamma contributes a coefficient of two. The exact finite
reciprocal correction contributes ((N+2)K^2). Removing the auxiliary
diagonal error preserves the two ordinary dyadic observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalSlope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNegativeCriticalCorrection (correction guard)
open GaussianGammaNegativeCriticalCorrectionSlope (ordered domain budget rowBudget correction_distance)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData name_regular shifted_source)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedRealOrderTransport (upperSlack remove_upper_slack)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingTailComparison (point_add_upper_same)
open RationalValueBounds (upper upper_mono upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def coefficient (N K : PTm n) : PTm n := two+succ (succ N)*(K*K)
def cap (a c N K : PTm n) : PTm n := coefficient N K*monus c a
def raw (p a b N : PTm n) : PTm n := qadd (ap2 DF p (dd (b+a) b)) (correction a b N)

@[simp] theorem subst_coefficient {k : ℕ} (σ : Fin n → PTm k) (N K : PTm n) :
    Syn.subst σ (coefficient N K) = coefficient (Syn.subst σ N) (Syn.subst σ K) := by simp [coefficient]
@[simp] theorem subst_cap {k : ℕ} (σ : Fin n → PTm k) (a c N K : PTm n) :
    Syn.subst σ (cap a c N K) = cap (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) (Syn.subst σ K) :=
  by simp [cap]

theorem left_guard (a c b : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] guard a b :=
  .andI h.andE₁ (lt_of_le_of_lt h.andE₂.andE₁ h.andE₂.andE₂)

theorem right_guard (a c b : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] guard c b :=
  .andI (le_trans h.andE₁ h.andE₂.andE₁) h.andE₂.andE₂

theorem raw_error (p a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b N)) (raw p a b N) three (unit p) :=
  distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p (correction a b N))) (.eqRefl _) (.eqRefl _)
    (add_sample_error DF constantF (dd (b+a) b) (correction a b N) p
      (GaussianGammaDigammaNative.name_regular _ _ (shifted_source a b h)) (constant_regular _))

private theorem shifted_budget (p a c b : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd (b+c) b))) (fstT (ap2 DF p (dd (b+a) b)))
      (two*monus c a*unit p+two*b) (b*unit p) := by
  have hb := GaussianGammaNegativeCriticalCorrectionSlope.denominator_positive a c b h
  have hu := unit_positive (Γ := Γ) p
  have hbc : Γ ⊢[PRAAx] le (b+a) (b+c) := by ipra_le sl h.andE₂.andE₁
  have direct := GaussianGammaDigammaLipschitz.unit_upper_at p p (b+a) (b+c) b hb (le_add_right _ _) hbc
  have e := natEq (((congrMonus (add_comm b c) (add_comm b a)).eqTrans (monus_add_add c a b)) :
    Γ ⊢[PRAAx] monus (b+c) (b+a) ≐ monus c a)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hb hu) hu) direct
    (by dsimp only [rateNumerator,rateDenominator]; ipra_le 0 with -2*𝔞(b)*𝔞(unit p)^3*e)

private theorem raw_diagonal (p a c b N K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] upper (fstT (raw p c b N)) (fstT (raw p a b N))
      (cap a c N K*unit p+two*b) (b*unit p) := by
  let R := budget a c N K
  let U := unit p
  have hb := GaussianGammaNegativeCriticalCorrectionSlope.denominator_positive a c b h.andE₁
  have hD := positive_product b U hb (unit_positive p)
  have old := scalar_upper _ _ R b hb (correction_distance a c b N K h)
  have scaled := upper_mono _ _ R b (R*U) (b*U) hb old (by ipra_le 0)
  have joined := point_add_upper_same _ _ _ _ _ _ _ hD (shifted_budget p a c b h.andE₁) scaled
  exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [R,U,cap,coefficient,budget,rowBudget]; ipra_ring) (.eqRefl _) joined

private theorem diagonal_upper (p a c b N K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] upper (fstT (ap2 nameF p (nameData c b N))) (fstT (ap2 nameF p (nameData a b N)))
      (cap a c N K*unit p+num 8*b) (b*unit p) := by
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have hb := GaussianGammaNegativeCriticalCorrectionSlope.denominator_positive a c b h.andE₁
  have l := scalar_upper _ _ _ _ hu (raw_error p c b N (right_guard a c b h.andE₁))
  have rr := raw_error p a b N (left_guard a c b h.andE₁)
  have r := scalar_upper _ _ _ _ hu (distance_symmetric _ _ _ _ hu rr)
  have m := raw_diagonal p a c b N K h
  have j := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l m) r
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hu (positive_product _ _ hb hu)) hu)
    j (by unfold three; ipra_le 0)

private theorem cofinal_upper (p q t a c b N K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] upperSlack (fstT (ap2 nameF p (nameData c b N))) (fstT (ap2 nameF q (nameData a b N)))
      (rateNumerator (cap a c N K) b p q) (rateDenominator b p q) (num 10) t := by
  have hb := GaussianGammaNegativeCriticalCorrectionSlope.denominator_positive a c b h.andE₁
  have hu := unit_positive (Γ := Γ) t
  have lp := positive_product _ _ (unit_positive p) hu
  have rp := positive_product _ _ hu (unit_positive q)
  have cp := positive_product _ _ hb hu
  have l := scalar_upper _ _ _ _ lp (point_at nameF (nameData c b N) p t
    (name_regular c b N (right_guard a c b h.andE₁)))
  have r := scalar_upper _ _ _ _ rp (point_at nameF (nameData a b N) t q
    (name_regular a b N (left_guard a c b h.andE₁)))
  have m := diagonal_upper t a c b N K h
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ lp cp) rp)
    (upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l m) r)
    (by dsimp only [upperSlack,rateNumerator,rateDenominator]; ipra_le 0)

theorem upper_at (p q a c b N K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] upper (fstT (ap2 nameF p (nameData c b N))) (fstT (ap2 nameF q (nameData a b N)))
      (rateNumerator (cap a c N K) b p q) (rateDenominator b p q) :=
  remove_upper_slack _ _ _ _ (num 10) (cofinal_upper p q _ a c b N K h)

theorem original_shifted_negative_digamma_upper_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (domain (var 0) (var 1) (var 2) (var 4) ⟶
      upper (fstT (ap2 nameF (var 5) (nameData (var 1) (var 2) (var 3))))
        (fstT (ap2 nameF (var 6) (nameData (var 0) (var 2) (var 3))))
        (rateNumerator (cap (var 0) (var 1) (var 3) (var 4)) (var 2) (var 5) (var 6))
        (rateDenominator (var 2) (var 5) (var 6))) :=
  closeUniv 7 (.impI (upper_at _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalSlope
