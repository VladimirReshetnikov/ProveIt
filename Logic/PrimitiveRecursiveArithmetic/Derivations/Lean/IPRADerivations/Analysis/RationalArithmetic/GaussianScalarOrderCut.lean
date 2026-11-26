import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSyntheticBounds
import IPRADerivations.Core.LinearCombination

/-!
# Scalar radius cuts and actual two-name Gaussian order

The radius is an actual rational scalar code. Its nonnegativity is part
of the norm comparison, so squaring cannot introduce negative radii.
For a supplied natural fraction representation, this comparison is exactly
the original rational Euclidean bound. Actual scalar additions provide the
two independent dyadic slacks in the represented Gaussian/scalar order.
Only fixed PR schemas are external; both persistent inputs and all
fractions, moduli and precision indices remain numerical object inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarOrderCut

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product scalar_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode natCode_represents)
open LeanProofs.IPRA.Analysis.RationalArithmetic (represents add multiply)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def normLE (g r : PTm n) : Fm PTm n :=
  rationalLE (natCode zero) r ⋏ rationalLE (qnormSq g) (multiply r r)
def unitCode (k : PTm n) : PTm n := normalize (ZT.ofNat one) (unit k)
def slackScalar (r k j : PTm n) : PTm n := add r (add (unitCode k) (unitCode j))
def jointCut (g rhs : PR 2) (gx rx : PTm n) : Fm PTm n := .all (.all
  (normLE (ap2 g (var 1) (Syn.shift (Syn.shift gx)))
    (slackScalar (ap2 rhs (var 0) (Syn.shift (Syn.shift rx))) (var 1) (var 0))))

@[simp] theorem subst_normLE {m : ℕ} (σ : Fin n → PTm m) (g r : PTm n) :
    (normLE g r).subst σ = normLE (Syn.subst σ g) (Syn.subst σ r) := by simp [normLE]
@[simp] theorem subst_unitCode {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (unitCode k) = unitCode (Syn.subst σ k) := by simp [unitCode]
@[simp] theorem subst_slackScalar {m : ℕ} (σ : Fin n → PTm m) (r k j : PTm n) :
    Syn.subst σ (slackScalar r k j) = slackScalar (Syn.subst σ r) (Syn.subst σ k) (Syn.subst σ j) := by simp [slackScalar]
@[simp] theorem subst_jointCut {m : ℕ} (σ : Fin n → PTm m) (g rhs : PR 2) (gx rx : PTm n) :
    (jointCut g rhs gx rx).subst σ = jointCut g rhs (Syn.subst σ gx) (Syn.subst σ rx) := by
  simp [jointCut,Syn.subst_shift,Syn.shift_subst]

theorem normLE_congr {g g' r r' : PTm n} (hg : Γ ⊢[PRAAx] g ≐ g') (hr : Γ ⊢[PRAAx] r ≐ r')
    (h : Γ ⊢[PRAAx] normLE g r) : Γ ⊢[PRAAx] normLE g' r' := by
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (normLE (var 0) (var 1) : Fm PTm 2)
    ![g,r] ![g',r'] (fun i => by fin_cases i; exact hg; exact hr) (by simpa using h)
  simpa using e

theorem scalar_nonnegative (r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) : Γ ⊢[PRAAx] rationalLE (natCode zero) r :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ one B (le_refl _) hB (natCode_represents zero) hr
    (le_congr (by ipra_ring) (by ipra_ring) (zero_le A))

/-- Actual scalar multiplication has exactly the normalized squared radius,
even when the original radius code is not stored canonically. -/
theorem scalar_square (r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) : Γ ⊢[PRAAx]
    multiply r r ≐ squaredTolerance A B := by
  have value := RationalRepresentations.represents_multiply (Γ := Γ) r r _ _ _ _ hr hr
  have positive := positive_product (Γ := Γ) _ _ hB hB
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ positive) value
    (GaussianRationalMetric.squared_tolerance_represents A B hB) positive positive
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem normLE_from_bound (g r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) (h : Γ ⊢[PRAAx] bounded g A B) : Γ ⊢[PRAAx] normLE g r :=
  .andI (scalar_nonnegative r A B hB hr)
    (RationalArgmin.rationalLE_congr (.eqRefl _) (scalar_square r A B hB hr).eqSymm h)

theorem bound_from_normLE (g r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) (h : Γ ⊢[PRAAx] normLE g r) : Γ ⊢[PRAAx] bounded g A B :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (scalar_square r A B hB hr) (Prf.andE₂ h)

theorem normLE_iff (g r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) : Γ ⊢[PRAAx] Fm.iff (normLE g r) (bounded g A B) :=
  .iffI (.impI (bound_from_normLE _ _ _ _ hB.wk hr.wk Prf.hyp0))
    (.impI (normLE_from_bound _ _ _ _ hB.wk hr.wk Prf.hyp0))

theorem unitCode_represents (k : PTm n) : Γ ⊢[PRAAx] represents (unitCode k) (ZT.ofNat one) (unit k) :=
  normalize_preserves_value _ _ (unit_positive k)

theorem slackScalar_represents (r R S k j : PTm n)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat R) S) : Γ ⊢[PRAAx]
    represents (slackScalar r k j) (ZT.ofNat (R*unit k*unit j+S*(unit j+unit k))) (S*unit k*unit j) := by
  have inner := RationalRepresentations.represents_add (Γ := Γ) (unitCode k) (unitCode j) _ _ _ _
    (unitCode_represents k) (unitCode_represents j)
  have outer := RationalRepresentations.represents_add (Γ := Γ) r (add (unitCode k) (unitCode j)) _ _ _ _ hr inner
  apply scalar_congr (.eqRefl _) (hAB := by ipra_ring) (h := outer)
  ipra_lc

theorem slack_denominator_positive (S k j : PTm n) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    le one (S*unit k*unit j) := positive_product _ _ (positive_product _ _ hS (unit_positive k)) (unit_positive j)

theorem slack_normLE_from_bound (g r R S k j : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat R) S)
    (h : Γ ⊢[PRAAx] bounded g (R*unit k*unit j+S*(unit j+unit k)) (S*unit k*unit j)) : Γ ⊢[PRAAx]
    normLE g (slackScalar r k j) :=
  normLE_from_bound _ _ _ _ (slack_denominator_positive S k j hS) (slackScalar_represents r R S k j hr) h

theorem joint_at (g rhs : PR 2) (gx rx k j : PTm n) (h : Γ ⊢[PRAAx] jointCut g rhs gx rx) : Γ ⊢[PRAAx]
    normLE (ap2 g k gx) (slackScalar (ap2 rhs j rx) k j) := by
  have first : Γ ⊢[PRAAx] .all (normLE (ap2 g (Syn.shift k) (Syn.shift gx))
      (slackScalar (ap2 rhs (var 0) (Syn.shift rx)) (Syn.shift k) (var 0))) := by
    simpa only [jointCut,Fm.subst_all,subst_normLE,subst_slackScalar,subst_ap2,Syn.subst_var,
      Syn.up_zero,Syn.up_one,Syn.up_succ,Foundations.BoundedFormulas.subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE k
  simpa only [subst_normLE,subst_slackScalar,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using first.allE j

def slackF : PR 3 := PTm.toPR (slackScalar (var 0) (var 1) (var 2))
theorem slack_program (r k j : PTm n) : Γ ⊢[PRAAx] ap3 slackF r k j ≐ slackScalar r k j := by
  simpa only [slackF,ap3,subst_slackScalar,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (slackScalar (var 0) (var 1) (var 2) : PTm 3) ![r,k,j]

theorem scalar_norm_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ represents (var 1) (ZT.ofNat (var 2)) (var 3) ⟶
      Fm.iff (normLE (var 0) (var 1)) (bounded (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (normLE_iff _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem scalar_slack_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (represents (var 0) (ZT.ofNat (var 1)) (var 2) ⟶
      represents (slackScalar (var 0) (var 3) (var 4))
        (ZT.ofNat (var 1*unit (var 3)*unit (var 4)+var 2*(unit (var 4)+unit (var 3))))
        (var 2*unit (var 3)*unit (var 4))) :=
  closeUniv 5 (.impI (slackScalar_represents _ _ _ _ _ Prf.hyp0))

theorem joint_cut_observation_closed (g rhs : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (jointCut g rhs (var 0) (var 1) ⟶ normLE (ap2 g (var 2) (var 0))
      (slackScalar (ap2 rhs (var 3) (var 1)) (var 2) (var 3))) :=
  closeUniv 4 (.impI (joint_at _ _ _ _ _ _ Prf.hyp0))

theorem scalar_slack_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 slackF (var 0) (var 1) (var 2) ≐ slackScalar (var 0) (var 1) (var 2)) :=
  closeUniv 3 (slack_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarOrderCut
