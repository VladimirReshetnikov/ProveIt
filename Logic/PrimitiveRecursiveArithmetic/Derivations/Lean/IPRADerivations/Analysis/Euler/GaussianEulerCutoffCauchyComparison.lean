import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperTailCauchyBudget

/-!
# Varying-cutoff Euler comparison conditional only on the lower tail

The sole additional predicate states the still-separate original named
lower-tail estimate on the exact lowerData returned by the cutoff split.
The actual upper bound, actual raw split, and original combined cutoff
budget derive the full comparison. No Cauchy or returned-name law is a
premise. Outer cutoff p is unchanged; compact observation precision is p+4.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCutoffCauchyComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactAdditivity (nameF)
open GaussianGammaCompactCutoffSplit (lowerData upperData rawSum)
open GaussianGammaIntegralCutoffs (height tailCoefficient)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (qzero qadd positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (point_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def oldData (z R B k A : PTm n) : PTm n := GaussianGammaEulerCompactQuadrature.data z R B k A
def observation (p z R B k A : PTm n) : PTm n := ap2 nameF p (oldData z R B k A)
def lowerBody (z R B A p k j : PTm n) : Fm PTm n := le k j ⟶
  bounded (ap2 nameF p (lowerData z R B k j A)) (A*unit p+unit (height k A R)) (unit (height k A R)*unit p)
def lowerTailBound (z R B A : PTm n) : Fm PTm n := .all (.all (.all
  (lowerBody (Syn.shift (Syn.shift (Syn.shift z))) (Syn.shift (Syn.shift (Syn.shift R)))
    (Syn.shift (Syn.shift (Syn.shift B))) (Syn.shift (Syn.shift (Syn.shift A))) (var 2) (var 1) (var 0))))
def input (z R B A : PTm n) : Fm PTm n := GaussianGammaEulerCompactQuadrature.source z R B ⋏ (le one A ⋏ lowerTailBound z R B A)
def combined (A R : PTm n) : PTm n := A+tailCoefficient R
def pairNumerator (s t k A R : PTm n) : PTm n := combined A R*unit s*unit t+unit (height k A R)*(unit t+num 9*unit s)
def pairDenominator (s t k A R : PTm n) : PTm n := unit (height k A R)*unit s*unit t
def clock (p : PTm n) : PTm n := p+num 4

@[simp] theorem subst_oldData {m : ℕ} (σ : Fin n → PTm m) (z R B k A : PTm n) :
    Syn.subst σ (oldData z R B k A) = oldData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ A) := by simp [oldData]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B k A : PTm n) :
    Syn.subst σ (observation p z R B k A) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ A) := by simp [observation]
@[simp] theorem subst_lowerBody {m : ℕ} (σ : Fin n → PTm m) (z R B A p k j : PTm n) :
    (lowerBody z R B A p k j).subst σ = lowerBody (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A)
      (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ j) := by
  simp [lowerBody,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_lowerTailBound {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    (lowerTailBound z R B A).subst σ = lowerTailBound (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [lowerTailBound,Syn.subst_shift,Syn.shift_subst,Syn.up]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    (input z R B A).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [input]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) : Syn.subst σ (clock p) = clock (Syn.subst σ p) := by simp [clock]

theorem lower_bound_at (z R B A p k j : PTm n) (h : Γ ⊢[PRAAx] lowerTailBound z R B A) (hkj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (lowerData z R B k j A)) (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) := by
  have rule : Γ ⊢[PRAAx] lowerBody z R B A p k j := by
    simpa only [lowerTailBound,Fm.subst_all,subst_lowerBody,Foundations.BoundedFormulas.subst_up_shift',
      Syn.subst_var,GaussianCompactRiemannName.up_two,Syn.up_one,Syn.up_zero,Syn.up_succ,Syn.inst_zero,Syn.inst_succ,
      Syn.subst_inst_shift,Syn.shift_var] using ((h.allE p).allE k).allE j
  exact .impE rule hkj

theorem split_input (z R B A k j : PTm n) (h : Γ ⊢[PRAAx] input z R B A) (hkj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    GaussianGammaCompactCutoffSplit.source z R B k j A := .andI h.andE₁ (.andI h.andE₂.andE₁ hkj)

theorem observation_canonical (p z R B k A : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (observation p z R B k A) :=
  GaussianCompactRiemannName.name_canonical GaussianEulerIntegrandName.evaluatorF p _ _ _ _ _ _

/-- Only the exact original lowerData bound is conditional. Both tail
observations are kept at the same actual requested precision t. -/
theorem tail_sum_distance (t z R B k j A : PTm n) (h : Γ ⊢[PRAAx] input z R B A) (hkj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    distanceBounded (rawSum t z R B k j A) (observation t z R B k A)
      (combined A R*unit t+two*unit (height k A R)) (unit (height k A R)*unit t) := by
  let D := unit (height k A R)*unit t
  let old := observation t z R B k A
  have dp := positive_product (Γ := Γ) _ _ (unit_positive (height k A R)) (unit_positive t)
  have low := lower_bound_at z R B A t k j h.andE₂.andE₂ hkj
  have upRaw := GaussianEulerNamedUpperTail.original_named_upper_tail t z R B k j A (split_input z R B A k j h hkj)
  have up := GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (congrAdd (congrMul (GaussianEulerUpperTailCauchyBudget.exact_tail_coefficient R).eqSymm (.eqRefl (unit t))) (.eqRefl _)) (.eqRefl _) upRaw
  have lowD := (GaussianReconstructionRoots.distance_zero_iff _ _ _ dp).iffMpr low
  have upD := (GaussianReconstructionRoots.distance_zero_iff _ _ _ dp).iffMpr up
  have held := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) old D dp
  have inner := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ dp held upD
  have inner' := distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right old (observation_canonical t z R B k A)) (.eqRefl _) (.eqRefl _) inner
  have outer := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ dp lowD inner'
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qzero_add old (observation_canonical t z R B k A))
    (by unfold combined; ipra_ring) (.eqRefl _) outer

/-- Actual later and earlier cutoff observations. The combined original
(A+tailCoefficient)/2^height term is preserved, together with eps_s+9eps_t. -/
theorem pair_bound (s t z R B k j A : PTm n) (h : Γ ⊢[PRAAx] input z R B A) (hkj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    distanceBounded (observation s z R B j A) (observation t z R B k A) (pairNumerator s t k A R) (pairDenominator s t k A R) := by
  have us := unit_positive (Γ := Γ) s
  have ut := unit_positive (Γ := Γ) t
  have uh := unit_positive (Γ := Γ) (height k A R)
  have oldD := positive_product (Γ := Γ) _ _ us ut
  have tailD := positive_product (Γ := Γ) _ _ uh ut
  have den : Γ ⊢[PRAAx] le one (pairDenominator s t k A R) := positive_product _ _ (positive_product _ _ uh us) ut
  have raw := GaussianGammaCompactCutoffSplit.raw_observations s t z R B k j A (split_input z R B A k j h hkj)
  have tails := tail_sum_distance t z R B k j A h hkj
  have first := distance_radius_mono _ _ _ _ ((unit t+num 7*unit s)*unit (height k A R)) (pairDenominator s t k A R)
    oldD den (le_of_eq_add (d := zero) (by unfold pairDenominator; ipra_ring)) raw
  have second := distance_radius_mono _ _ _ _ ((combined A R*unit t+two*unit (height k A R))*unit s) (pairDenominator s t k A R)
    tailD den (le_of_eq_add (d := zero) (by unfold pairDenominator; ipra_ring)) tails
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold pairNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first second)

theorem clock_unit (p : PTm n) : Γ ⊢[PRAAx] unit (clock p) ≐ unit p*num 16 :=
  (pw_add two p (num 4)).eqTrans (congrMul (.eqRefl _) GaussianFiniteLogarithmDyadicTail.two_four)

theorem cutoff_clock_budget (k A R : PTm n) : Γ ⊢[PRAAx] le (combined A R*unit (clock k)) (unit (height k A R)) := by
  have later : Γ ⊢[PRAAx] le (clock k) (k+num 6) := le_of_eq_add (d := two) (by unfold clock; ipra_ring)
  have smaller := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (combined A R)) (GaussianExponentialReference.unit_monotone later)
  exact le_trans smaller (le_of_lt (GaussianGammaIntegralCutoffs.omitted_tail_budget k A R))

/-- The returned compact observation clock p+4 is an actual derived
precision formula. No regularity of the varying output is a premise. -/
theorem ordered_clock_comparison (k j z R B A : PTm n) (h : Γ ⊢[PRAAx] input z R B A) (hkj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    distanceBounded (observation (clock j) z R B j A) (observation (clock k) z R B k A) (unit k+unit j) (unit k*unit j) := by
  have raw := pair_bound (clock j) (clock k) z R B k j A h hkj
  have dp : Γ ⊢[PRAAx] le one (pairDenominator (clock j) (clock k) k A R) :=
    positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
  have dc := positive_product (Γ := Γ) _ _ (unit_positive (clock j)) (unit_positive (clock k))
  have bound : Γ ⊢[PRAAx] le (pairNumerator (clock j) (clock k) k A R)
      (unit (height k A R)*(unit (clock k)+num 10*unit (clock j))) := by
    unfold pairNumerator
    ipra_le 𝔞(unit (clock j))*sl (cutoff_clock_budget (Γ := Γ) k A R)
  have reduced := distance_radius_mono _ _ _ _ (unit (clock k)+num 10*unit (clock j)) (unit (clock j)*unit (clock k)) dp dc
    (le_congr (.eqRefl _) (by unfold pairDenominator; ipra_ring) (mul_le_mul_right (unit (clock j)*unit (clock k)) bound)) raw
  apply distance_radius_mono _ _ _ _ _ _ dc (positive_product _ _ (unit_positive k) (unit_positive j)) _ reduced
  have ek := natEq (clock_unit (Γ := Γ) k)
  have ej := natEq (clock_unit (Γ := Γ) j)
  refine le_of_eq_add (d := num 240*unit k*unit k*unit j+num 96*unit k*unit j*unit j) ?_
  apply deriveNat
  ipra_simps
  rw [ek,ej]
  ring

def clockF : PR 1 := PTm.toPR (clock (var 0))
theorem clock_at (p : PTm n) : Γ ⊢[PRAAx] ap1 clockF p ≐ clock p := by
  simpa [clockF,ap1] using toPR_eq (Γ := Γ) (clock (var 0) : PTm 1) ![p]

theorem actual_lower_tail_predicate_elimination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lowerTailBound (var 0) (var 1) (var 2) (var 3) ⟶ le (var 5) (var 6) ⟶
      bounded (ap2 nameF (var 4) (lowerData (var 0) (var 1) (var 2) (var 5) (var 6) (var 3)))
        (var 3*unit (var 4)+unit (height (var 5) (var 3) (var 1)))
        (unit (height (var 5) (var 3) (var 1))*unit (var 4))) :=
  closeUniv 7 (.impI (.impI (lower_bound_at _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem conditional_original_cutoff_pair_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 2) (var 3) (var 4) (var 7) ⟶ le (var 5) (var 6) ⟶
      distanceBounded (observation (var 0) (var 2) (var 3) (var 4) (var 6) (var 7))
        (observation (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))
        (pairNumerator (var 0) (var 1) (var 5) (var 7) (var 3))
        (pairDenominator (var 0) (var 1) (var 5) (var 7) (var 3))) :=
  closeUniv 8 (.impI (.impI (pair_bound _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem conditional_original_ordered_cutoff_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 2) (var 3) (var 4) (var 5) ⟶ le (var 0) (var 1) ⟶
      distanceBounded (observation (clock (var 1)) (var 2) (var 3) (var 4) (var 1) (var 5))
        (observation (clock (var 0)) (var 2) (var 3) (var 4) (var 0) (var 5))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (.impI (ordered_clock_comparison _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_cutoff_observation_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 clockF (var 0) ≐ var 0+num 4) := closeUniv 1 (clock_at _)
theorem actual_original_cutoff_clock_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (unit (clock (var 0)) ≐ unit (var 0)*num 16) := closeUniv 1 (clock_unit _)

end LeanProofs.IPRA.Analysis.GaussianEulerCutoffCauchyComparison
