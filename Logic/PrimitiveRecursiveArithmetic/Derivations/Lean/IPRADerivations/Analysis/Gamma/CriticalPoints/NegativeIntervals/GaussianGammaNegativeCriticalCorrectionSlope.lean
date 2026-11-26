import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalCorrection
import IPRADerivations.Analysis.Stirling.Wallis.GaussianGammaHalfWallisRate
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# Finite slope of the negative-interval reciprocal correction

Every correction term is increasing. When the two rational endpoints
are separated from both poles by at least (1/K), each term changes
by at most (K^2(c-a)/b). The summation keeps the true internal count
(N+2), including the reciprocal with denominator (a) or (c).
-/

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalCorrectionSlope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaNegativeCriticalCorrection
  (row body bottomDen positiveSum correction den_expand row_den_positive row_at prefix_succ)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingTailComparison (point_order_refl point_add_order)
open RationalArgmin (rationalLE rationalLE_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def ordered (a c b : PTm n) : Fm PTm n := le one a ⋏ (le a c ⋏ lt c b)
def domain (a c b K : PTm n) : Fm PTm n :=
  ordered a c b ⋏ (le b (K*a) ⋏ le b (K*monus b c))
def rowBudget (a c K : PTm n) : PTm n := (K*K)*monus c a
def budget (a c N K : PTm n) : PTm n := succ (succ N)*rowBudget a c K

@[simp] theorem subst_ordered {k : ℕ} (σ : Fin n → PTm k) (a c b : PTm n) :
    (ordered a c b).subst σ = ordered (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) := by simp [ordered]
@[simp] theorem subst_domain {k : ℕ} (σ : Fin n → PTm k) (a c b K : PTm n) :
    (domain a c b K).subst σ = domain (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ K) := by simp [domain]
@[simp] theorem subst_rowBudget {k : ℕ} (σ : Fin n → PTm k) (a c K : PTm n) :
    Syn.subst σ (rowBudget a c K) = rowBudget (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ K) := by simp [rowBudget]
@[simp] theorem subst_budget {k : ℕ} (σ : Fin n → PTm k) (a c N K : PTm n) :
    Syn.subst σ (budget a c N K) = budget (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) (Syn.subst σ K) :=
  by simp [budget]

theorem denominator_positive (a c b : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] le one b :=
  le_trans h.andE₁ (le_trans h.andE₂.andE₁ (le_of_lt h.andE₂.andE₂))

private theorem den_gap (a c b j : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] bottomDen a b j ≐ bottomDen c b j+monus c a := by
  have hcb : Γ ⊢[PRAAx] le c (succ j*b) :=
    le_trans (le_of_lt h.andE₂.andE₂) (by ipra_le 𝔞(j)*𝔞(b))
  have ec := natEq (eq_add_of_le hcb)
  have ea := natEq (eq_add_of_le (le_trans h.andE₂.andE₁ hcb))
  have ed := natEq (eq_add_of_le h.andE₂.andE₁)
  unfold bottomDen
  apply deriveNat
  ipra_simps
  linear_combination -ea+ec+ed

theorem row_monotone (a c b j : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] rationalLE (fstT (row a b j)) (fstT (row c b j)) := by
  let P := bottomDen c b j
  let Q := bottomDen a b j
  have hp := row_den_positive c b j h.andE₂.andE₂
  have hq := row_den_positive a b j (lt_of_le_of_lt h.andE₂.andE₁ h.andE₂.andE₂)
  have e := natEq (den_gap a c b j h)
  exact fractions_order b Q b P hq hp (by ipra_le 𝔞(b)*𝔞(monus c a) with 𝔞(b)*e)

def prefixOrder (a c b j : PTm n) : Fm PTm n :=
  rationalLE (fstT (positiveSum a b j)) (fstT (positiveSum c b j))

@[simp] theorem subst_prefixOrder {k : ℕ} (σ : Fin n → PTm k) (a c b j : PTm n) :
    (prefixOrder a c b j).subst σ = prefixOrder (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ j) :=
  by simp [prefixOrder]

private theorem prefix_zero (a c b : PTm n) : Γ ⊢[PRAAx] prefixOrder a c b zero :=
  rationalLE_congr (congrFst (GaussianRationalFiniteSum.sum_zero body (pairT a b))).eqSymm
    (congrFst (GaussianRationalFiniteSum.sum_zero body (pairT c b))).eqSymm (point_order_refl qzero)

private theorem prefix_step (a c b j : PTm n) (h : Γ ⊢[PRAAx] ordered a c b)
    (ih : Γ ⊢[PRAAx] prefixOrder a c b j) : Γ ⊢[PRAAx] prefixOrder a c b (succ j) :=
  rationalLE_congr (congrFst (prefix_succ a b j)).eqSymm (congrFst (prefix_succ c b j)).eqSymm
    (point_add_order _ _ _ _ ih (row_monotone a c b j h))

theorem prefix_monotone (a c b N : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] prefixOrder a c b N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] ordered (Syn.shift a) (Syn.shift c) (Syn.shift b) :=
    by simpa only [Fm.shift,Syn.shift,subst_ordered] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixOrder (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ (by simp [prefixOrder,rationalLE,le_QF]) ?_ ?_
    · simpa only [subst_prefixOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) a c b
    · simpa only [subst_prefixOrder,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0) hs.wk Prf.hyp0
  simpa only [subst_prefixOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem correction_monotone (a c b N : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] rationalLE (fstT (correction a b N)) (fstT (correction c b N)) := by
  have ha := h.andE₁
  have hc := le_trans ha h.andE₂.andE₁
  have e := fractions_order b c b a hc ha (by ipra_le 𝔞(b)*sl h.andE₂.andE₁)
  have neg : Γ ⊢[PRAAx] rationalLE (fstT (qnegative (fraction b a))) (fstT (qnegative (fraction b c))) :=
    rationalLE_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (RationalAlgebra.negative_antitone _ _ e)
  exact point_add_order (positiveSum a b (succ N)) (positiveSum c b (succ N))
    (qnegative (fraction b a)) (qnegative (fraction b c)) (prefix_monotone a c b (succ N) h) neg

private theorem reciprocal_distance (b P Q K gap : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hp : Γ ⊢[PRAAx] le one P) (hq : Γ ⊢[PRAAx] le one Q)
    (kp : Γ ⊢[PRAAx] le b (K*P)) (kq : Γ ⊢[PRAAx] le b (K*Q))
    (eq : Γ ⊢[PRAAx] Q ≐ P+gap) :
    Γ ⊢[PRAAx] distanceBounded (fraction b P) (fraction b Q) ((K*K)*gap) b := by
  have e := natEq eq
  have prod := le_mul_mono kp kq
  exact GaussianGammaHalfWallisRate.fraction_distance b P b Q _ b hp hq hb
    (by ipra_le 𝔞(gap)*sl prod with -𝔞(b)^2*e)
    (by ipra_le 𝔞(b)^2*𝔞(gap)+𝔞(K)^2*𝔞(gap)*𝔞(P)*𝔞(Q) with 𝔞(b)^2*e)

theorem row_distance (a c b j K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] distanceBounded (row c b j) (row a b j) (rowBudget a c K) b := by
  let P := bottomDen c b j
  let Q := bottomDen a b j
  have hc := h.andE₁.andE₂.andE₂
  have hp := row_den_positive c b j hc
  have hq := row_den_positive a b j (lt_of_le_of_lt h.andE₁.andE₂.andE₁ hc)
  have e := natEq (show Γ ⊢[PRAAx] P ≐ monus b c+j*b from den_expand c b j hc)
  have kp : Γ ⊢[PRAAx] le b (K*P) := by
    ipra_le sl h.andE₂.andE₂+𝔞(K)*𝔞(j)*𝔞(b) with 𝔞(K)*e
  have gap := den_gap a c b j h.andE₁
  have kq : Γ ⊢[PRAAx] le b (K*Q) := by
    have g := natEq (show Γ ⊢[PRAAx] Q ≐ P+monus c a from gap)
    ipra_le sl kp+𝔞(K)*𝔞(monus c a) with 𝔞(K)*g
  exact reciprocal_distance b P Q K (monus c a) (denominator_positive a c b h.andE₁) hp hq kp kq gap

theorem positive_sum_distance (a c b N K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] distanceBounded (positiveSum c b N) (positiveSum a b N) (N*rowBudget a c K) b := by
  have hb := denominator_positive a c b h.andE₁
  apply sum_distance body body N (pairT c b) (pairT a b) _ b hb
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift c) (Syn.shift b) (Syn.shift K) :=
    by simpa only [Fm.shift,Syn.shift,subst_domain] using h.shift
  simpa only [Syn.shift,subst_rowBudget,subst_pairT] using
    distance_congr (row_at (Syn.shift c) (Syn.shift b) (var 0)).eqSymm
      (row_at (Syn.shift a) (Syn.shift b) (var 0)).eqSymm (.eqRefl _) (.eqRefl _)
      (row_distance (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0) (Syn.shift K) hs.wk)

theorem correction_distance (a c b N K : PTm n) (h : Γ ⊢[PRAAx] domain a c b K) :
    Γ ⊢[PRAAx] distanceBounded (correction c b N) (correction a b N) (budget a c N K) b := by
  have hb := denominator_positive a c b h.andE₁
  have hc := h.andE₁.andE₂.andE₁
  have ha := h.andE₁.andE₁
  have kC : Γ ⊢[PRAAx] le b (K*c) := le_trans h.andE₂.andE₁ (by ipra_le 𝔞(K)*sl hc)
  have singular := reciprocal_distance b a c K (monus c a) hb ha (le_trans ha hc) h.andE₂.andE₁ kC (eq_add_of_le hc)
  have d := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hb
    (positive_sum_distance a c b (succ N) K h) (distance_symmetric _ _ _ _ hb singular)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget rowBudget; ipra_ring) (.eqRefl _) d

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalCorrectionSlope
