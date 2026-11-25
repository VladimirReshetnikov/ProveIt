import IPRADerivations.Analysis.GaussianGammaDigammaRecurrence
import IPRADerivations.Analysis.GaussianGammaEulerHeadQuadratic

/-!
# Digamma at positive integers

An object-level quantifier-free induction bounds each original
observation of ψ(n+1) against H_n minus the Euler constant. The
error bound is (2+5n)/2^p at observation p.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaInteger

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaDigammaRecurrence (digamma_shift)
open GaussianGammaHarmonicIncrement (reciprocalPoint harmonic_point_increment)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameRingLaws (three)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def nameF : PR 2 := addF negativeGammaF constantF
def data (i : PTm n) : PTm n := addData negativeGammaData (harmonicPoint i)
def value (p i : PTm n) : PTm n := ap2 DF p (dd (succ i) one)
def target (p i : PTm n) : PTm n := qadd (ap2 negativeGammaF p negativeGammaData) (harmonicPoint i)
def budget (i : PTm n) : PTm n := two+num 5*i
def errorLaw (p i : PTm n) : Fm PTm n := distanceBounded (value p i) (target p i) (budget i) (unit p)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (data i) = data (Syn.subst σ i) := by simp [data]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p i : PTm n) :
    Syn.subst σ (value p i) = value (Syn.subst σ p) (Syn.subst σ i) := by simp [value]
@[simp] theorem subst_target {m : ℕ} (σ : Fin n → PTm m) (p i : PTm n) :
    Syn.subst σ (target p i) = target (Syn.subst σ p) (Syn.subst σ i) := by simp [target]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (budget i) = budget (Syn.subst σ i) := by simp [budget]
@[simp] theorem subst_errorLaw {m : ℕ} (σ : Fin n → PTm m) (p i : PTm n) :
    (errorLaw p i).subst σ = errorLaw (Syn.subst σ p) (Syn.subst σ i) := by simp [errorLaw]

theorem integer_source (i : PTm n) : Γ ⊢[PRAAx] source (succ i) one :=
  .andI (zero_lt_succ i) (le_refl one)

theorem name_regular (i : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data i) :=
  add_fast _ _ _ _ negativeGamma_regular (constant_regular _)

private theorem diagonal_two (p s t : PTm n) (h : Γ ⊢[PRAAx] distanceBounded s t (unit p+unit p) (unit p*unit p)) :
    Γ ⊢[PRAAx] distanceBounded s t two (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem argument_step (i : PTm n) : Γ ⊢[PRAAx] dd (succ i+one) one ≐ dd (succ (succ i)) one := by
  have e : Γ ⊢[PRAAx] succ i+one ≐ succ (succ i) := by ipra_ring
  simpa only [GaussianGammaDigammaNative.subst_data,Syn.subst_var,Matrix.cons_val_zero,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    Prf.eqCongr (dd (var 0) one : PTm 1) (σ := ![succ i+one]) (σ' := ![succ (succ i)])
      (fun j => by fin_cases j; exact e)

theorem successor_error (p i : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (value p (succ i)) (qadd (value p i) (reciprocalPoint i)) (num 5) (unit p) := by
  let a := succ i
  have hs := integer_source (Γ := Γ) i
  have h1 := diagonal_two p _ _ (distance_congr (congrAp2 DF (.eqRefl p) (argument_step i)) (.eqRefl _)
    (.eqRefl _) (.eqRefl _) (cross_at _ _ _ _ p p (digamma_shift a one hs)))
  have c := GaussianGammaDigammaStep.unit_step_value a hs.andE₁
  have h2 := distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) ((constant_at p (fraction one a)).eqTrans c))
    (.eqRefl _) (.eqRefl _) (GaussianNameRingLaws.add_sample_error DF constantF (dd a one) (fraction one a) p
      (GaussianGammaDigammaNative.name_regular a one hs) (constant_regular _))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) h1 h2)

theorem error_base (p : PTm n) : Γ ⊢[PRAAx] errorLaw p zero := by
  let t := ap2 negativeGammaF p (negativeGammaData : PTm n)
  have c : Γ ⊢[PRAAx] GaussianRationalHorner.canonical t :=
    GaussianNameRingLaws.negative_canonical GaussianGammaCanonicalExponent.gammaF zero p
  have rule := (qadd_congr (.eqRefl t) GaussianGammaEulerHeadQuadratic.harmonic_zero).eqTrans
    (GaussianReciprocalHorner.qadd_zero_right t c)
  have small := diagonal_two p _ _ (cross_at _ _ _ _ p p (GaussianGammaDigammaNative.digamma_one (Γ := Γ)))
  exact distance_congr (.eqRefl _) rule.eqSymm (by unfold budget; ipra_ring) (.eqRefl _) small

theorem error_step (p i : PTm n) (ih : Γ ⊢[PRAAx] errorLaw p i) : Γ ⊢[PRAAx] errorLaw p (succ i) := by
  let t := ap2 negativeGammaF p (negativeGammaData : PTm n)
  have rule := (qadd_associative (Γ := Γ) t (harmonicPoint i) (reciprocalPoint i)).eqTrans
    (qadd_congr (.eqRefl _) (harmonic_point_increment i).eqSymm)
  have moved := distance_congr (.eqRefl _) rule (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.sum_left_error (value p i) (target p i) (reciprocalPoint i) (budget i) (unit p) (unit_positive p) ih)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (successor_error p i) moved)

theorem prefix_error (p i : PTm n) : Γ ⊢[PRAAx] errorLaw p i := by
  have hall : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using error_base (Γ := Γ) p
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using error_step (Syn.shift p) (var 0) Prf.hyp0
  simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

set_option maxHeartbeats 700000 in
theorem digamma_integer (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent DF nameF (dd (succ i) one) (data i) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget i+three)
    (GaussianGammaDigammaNative.name_regular _ _ (integer_source i)) (name_regular i) (.allI ?_)
  let j := Syn.shift i
  let p : PTm (n+1) := var 0
  let C := Γ.map Fm.shift
  have h1 := prefix_error (Γ := C) p j
  have h2 : C ⊢[PRAAx] distanceBounded (ap2 nameF p (data j)) (target p j) three (unit p) :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p (harmonicPoint j))) (.eqRefl _) (.eqRefl _)
      (GaussianNameRingLaws.add_sample_error negativeGammaF constantF negativeGammaData (harmonicPoint j) p
        negativeGamma_regular (constant_regular _))
  have res := distance_triangle_same (value p j) (target p j) (ap2 nameF p (data j)) (budget j) three (unit p)
    (unit_positive p) h1 (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (unit_positive p) h2)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,value,j,p,Syn.shift,subst_data,subst_budget,three,
    GaussianGammaDigammaNative.subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,PTm.subst_add] using res

theorem actual_original_integer_digamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent DF nameF (dd (succ (var 0)) one) (data (var 0))) :=
  closeUniv 1 (digamma_integer (var 0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaInteger
