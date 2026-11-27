import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementJet

/-! Data for the supplied candidate value and its first three logarithmic derivatives,
with an encoded compact-strip modulus for their actual divided quotients. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCandidateCalculus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasIntegerPeriod (input margin bound)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianRationalHorner (qzero)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "Log" => GaussianNamedPositiveLogarithm.nameF
local notation "logd" => GaussianNamedPositiveLogarithm.data

structure Candidate where
  value : PR 2
  first : PR 2
  second : PR 2
  third : PR 2
  valueData : PTm 2
  firstData : PTm 2
  secondData : PTm 2
  thirdData : PTm 2

def logData (c : Candidate) (A B : PTm n) : PTm n :=
  logd (input c.valueData A B) (margin c.valueData A B)

def regular (c : Candidate) (A B : PTm n) : Fm PTm n :=
  GaussianNamedPositiveLogarithm.source c.value (input c.valueData A B) (margin c.valueData A B) (bound c.valueData A B) ⋏
  (pointCN c.first (inst2 c.firstData A B) ⋏
  (pointCN c.second (inst2 c.secondData A B) ⋏
  (pointCN c.third (inst2 c.thirdData A B) ⋏ realOrder constantF c.third qzero (inst2 c.thirdData A B))))

def rates (c : Candidate) (p A B : PTm n) : Fm PTm n :=
  let C := succ A
  let h := step A C
  independentRate (Q (Log c.value) (Log c.value)) c.first
    (qd (Log c.value) (Log c.value) (logData c C B) (logData c A B) h B)
    (inst2 c.firstData A B) one (unit p) ⋏
  (independentRate (Q c.first c.first) c.second
    (qd c.first c.first (inst2 c.firstData C B) (inst2 c.firstData A B) h B)
    (inst2 c.secondData A B) one (unit p) ⋏
  independentRate (Q c.second c.second) c.third
    (qd c.second c.second (inst2 c.secondData C B) (inst2 c.secondData A B) h B)
    (inst2 c.thirdData A B) one (unit p))

def row (c : Candidate) (p A B : PTm n) : Fm PTm n :=
  regular c A B ⋏ (regular c (succ A) B ⋏ rates c p A B)

def tagSource (T M A B : PTm n) : Fm PTm n :=
  le one B ⋏ (le M B ⋏ (le ((T+one)*B) A ⋏ le (succ A) ((T+num 6)*B)))

/-- The supplied code admits all adjacent queries of step (1/B) in the compact strip
([T+1,T+6]), once (B) passes the supplied modulus. -/
def strip (c : Candidate) (p T M : PTm n) : Fm PTm n :=
  .all (.all (tagSource (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift M)) (var 1) (var 0) ⟶
    row c (Syn.shift (Syn.shift p)) (var 1) (var 0)))

@[simp] theorem subst_regular {m : ℕ} (σ : Fin n → PTm m) (c : Candidate) (A B : PTm n) :
    (regular c A B).subst σ = regular c (Syn.subst σ A) (Syn.subst σ B) := by
  simp [regular,input,margin,bound]

@[simp] theorem subst_rates {m : ℕ} (σ : Fin n → PTm m) (c : Candidate) (p A B : PTm n) :
    (rates c p A B).subst σ = rates c (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [rates,logData,input,margin,GaussianNamedDifferenceQuotient.data,GaussianNamedDifferenceQuotient.inverse,one]

@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (c : Candidate) (p A B : PTm n) :
    (row c p A B).subst σ = row c (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [row]

@[simp] theorem subst_tagSource {m : ℕ} (σ : Fin n → PTm m) (T M A B : PTm n) :
    (tagSource T M A B).subst σ = tagSource (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [tagSource,one]

@[simp] theorem subst_strip {m : ℕ} (σ : Fin n → PTm m) (c : Candidate) (p T M : PTm n) :
    (strip c p T M).subst σ = strip c (Syn.subst σ p) (Syn.subst σ T) (Syn.subst σ M) := by
  simp only [strip,Fm.subst_all,Fm.subst_imp,subst_tagSource,subst_row,Syn.up_zero,Syn.up_one,
    Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one,Foundations.BoundedFormulas.subst_up_shift']

theorem strip_at (c : Candidate) (p T M A B : PTm n)
    (h : Γ ⊢[PRAAx] strip c p T M) (ht : Γ ⊢[PRAAx] tagSource T M A B) : Γ ⊢[PRAAx] row c p A B := by
  have oneParam : Γ ⊢[PRAAx] .all (tagSource (Syn.shift T) (Syn.shift M) (Syn.shift A) (var 0) ⟶
      row c (Syn.shift p) (Syn.shift A) (var 0)) := by
    simpa only [strip,Fm.subst_all,Fm.subst_imp,subst_tagSource,subst_row,Syn.subst_var,Syn.up_zero,
      Syn.up_one,Syn.inst_zero,Foundations.BoundedFormulas.subst_up_shift',Syn.subst_inst_shift] using h.allE A
  have both : Γ ⊢[PRAAx] tagSource T M A B ⟶ row c p A B := by
    simpa only [Fm.subst_imp,subst_tagSource,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      oneParam.allE B
  exact .impE both ht

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCandidateCalculus
