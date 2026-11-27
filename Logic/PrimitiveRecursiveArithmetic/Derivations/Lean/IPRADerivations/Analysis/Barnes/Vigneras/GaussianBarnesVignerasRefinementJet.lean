import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementWrap
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasQuotientJet

/-! The three derivative observations use the same fine rational grid and clock as
the original quotient observations in the refinement wrapping certificate. -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementJet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasRefinementWrap (translation numerator observationClock)
open GaussianBarnesVignerasQuotientJet (firstF secondF thirdF)
open SignedDiscreteDerivativeOperators (divisor)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (x : PTm n) : PTm n := translation x+num 6

def candidate (t : PTm 2) (x k : PTm n) : PTm n := inst2 t (numerator x k) (divisor x)

def data1 (t : PTm 2) (x k : PTm n) : PTm n :=
  GaussianBarnesVignerasQuotientJet.data1 (numerator x k) (divisor x) (radius x) (candidate t x k)

def data2 (t : PTm 2) (x k : PTm n) : PTm n :=
  GaussianBarnesVignerasQuotientJet.data2 (numerator x k) (divisor x) (radius x) (candidate t x k)

def data3 (t : PTm 2) (x k : PTm n) : PTm n :=
  GaussianBarnesVignerasQuotientJet.data3 (numerator x k) (divisor x) (candidate t x k)

def firstBody (f : PR 2) (t : PTm 2) : PTm 2 :=
  ap2 (firstF f) (observationClock (var 1)) (data1 t (var 1) (var 0))

def secondBody (f : PR 2) (t : PTm 2) : PTm 2 :=
  ap2 (secondF f) (observationClock (var 1)) (data2 t (var 1) (var 0))

def thirdBody (f : PR 2) (t : PTm 2) : PTm 2 :=
  ap2 (thirdF f) (observationClock (var 1)) (data3 t (var 1) (var 0))

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (radius x) = radius (Syn.subst σ x) := by simp [radius,translation]

@[simp] theorem subst_candidate {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (x k : PTm n) :
    Syn.subst σ (candidate t x k) = candidate t (Syn.subst σ x) (Syn.subst σ k) := by simp [candidate]

@[simp] theorem subst_data1 {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (x k : PTm n) :
    Syn.subst σ (data1 t x k) = data1 t (Syn.subst σ x) (Syn.subst σ k) := by simp [data1]

@[simp] theorem subst_data2 {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (x k : PTm n) :
    Syn.subst σ (data2 t x k) = data2 t (Syn.subst σ x) (Syn.subst σ k) := by simp [data2]

@[simp] theorem subst_data3 {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (x k : PTm n) :
    Syn.subst σ (data3 t x k) = data3 t (Syn.subst σ x) (Syn.subst σ k) := by simp [data3]

theorem first_at (f : PR 2) (t : PTm 2) (x k : PTm n) :
    inst2 (firstBody f t) k x = ap2 (firstF f) (observationClock x) (data1 t x k) := by
  simp [inst2,firstBody]

theorem second_at (f : PR 2) (t : PTm 2) (x k : PTm n) :
    inst2 (secondBody f t) k x = ap2 (secondF f) (observationClock x) (data2 t x k) := by
  simp [inst2,secondBody]

theorem third_at (f : PR 2) (t : PTm 2) (x k : PTm n) :
    inst2 (thirdBody f t) k x = ap2 (thirdF f) (observationClock x) (data3 t x k) := by
  simp [inst2,thirdBody]

theorem successor_numerator (x k : PTm n) : Γ ⊢[PRAAx] numerator x (succ k) ≐ succ (numerator x k) := by
  unfold numerator GaussianBarnesVignerasIntegerPeriod.advance
  ipra_ring

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementJet
