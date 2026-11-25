import IPRADerivations.Analysis.GaussianNameRingLaws

/-!
# Finite iteration of exact equality of Gaussian names

At one common precision, the adjacent name equalities cost at most two
units of observation error per step. Only the resulting quantifier-free
numerical estimate is used in primitive-recursive induction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteEqualityChain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent diagonal_at cross_to_diagonal)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sample (f : PR 2) (t : PTm 2) (p j x : PTm n) : PTm n := ap2 f p (inst2 t j x)

def allSteps (f : PR 2) (t : PTm 2) (x : PTm n) : Fm PTm n :=
  .all (crossEquivalent f f (inst2 t (succ (var 0)) (Syn.shift x)) (inst2 t (var 0) (Syn.shift x)))

def estimate (f : PR 2) (t : PTm 2) (p j x : PTm n) : Fm PTm n :=
  distanceBounded (sample f t p j x) (sample f t p zero x) (two*j) (unit p)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (p j x : PTm n) :
    Syn.subst σ (sample f t p j x) = sample f t (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ x) := by
  simp [sample,subst_inst2]

@[simp] theorem subst_allSteps {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (x : PTm n) :
    (allSteps f t x).subst σ = allSteps f t (Syn.subst σ x) := by
  simp [allSteps,subst_inst2,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_estimate {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (p j x : PTm n) :
    (estimate f t p j x).subst σ = estimate f t (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ x) := by
  simp [estimate]

theorem step_at (f : PR 2) (t : PTm 2) (j x : PTm n) (h : Γ ⊢[PRAAx] allSteps f t x) :
    Γ ⊢[PRAAx] crossEquivalent f f (inst2 t (succ j) x) (inst2 t j x) := by
  simpa [allSteps,subst_inst2] using h.allE j

theorem estimate_zero (f : PR 2) (t : PTm 2) (p x : PTm n) : Γ ⊢[PRAAx] estimate f t p zero x := by
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero (sample f t p zero x) (unit p) (unit_positive _))

theorem estimate_succ (f : PR 2) (t : PTm 2) (p j x : PTm n) (h : Γ ⊢[PRAAx] allSteps f t x)
    (ih : Γ ⊢[PRAAx] estimate f t p j x) : Γ ⊢[PRAAx] estimate f t p (succ j) x := by
  have e := diagonal_at f f (inst2 t (succ j) x) (inst2 t j x) p
    (cross_to_diagonal _ _ _ _ (step_at f t j x h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) e ih)

theorem finite_estimate (f : PR 2) (t : PTm 2) (p j x : PTm n)
    (h : Γ ⊢[PRAAx] allSteps f t x) : Γ ⊢[PRAAx] estimate f t p j x := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] allSteps f t (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have hall : Γ ⊢[PRAAx] .all (estimate f t (Syn.shift p) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (by simp [estimate,distanceBounded,GaussianRationalMetric.bounded,RationalArgmin.rationalLE,Fm.QF,le_QF]) ?_ ?_
    · simpa only [subst_estimate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using estimate_zero (Γ := Γ) f t p x
    · simp only [subst_estimate,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact estimate_succ f t (Syn.shift p) (var 0) (Syn.shift x) h'.wk Prf.hyp0
  simpa only [subst_estimate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE j

theorem finite_cross (f : PR 2) (t : PTm 2) (j x : PTm n) (h : Γ ⊢[PRAAx] allSteps f t x)
    (hj : Γ ⊢[PRAAx] pointCN f (inst2 t j x)) (hz : Γ ⊢[PRAAx] pointCN f (inst2 t zero x)) :
    Γ ⊢[PRAAx] crossEquivalent f f (inst2 t j x) (inst2 t zero x) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (two*j) hj hz
  refine .allI ?_
  have h' : Γ.map Fm.shift ⊢[PRAAx] allSteps f t (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,estimate,sample,subst_inst2]
    using finite_estimate f t (var 0) (Syn.shift j) (Syn.shift x) h'

theorem actual_finite_named_equality_chain_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((allSteps f t (var 1) ⋏ (pointCN f (inst2 t (var 0) (var 1)) ⋏ pointCN f (inst2 t zero (var 1)))) ⟶
        crossEquivalent f f (inst2 t (var 0) (var 1)) (inst2 t zero (var 1))) :=
  closeUniv 2 (.impI (finite_cross f t _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteEqualityChain
