import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesVignerasLogQuotient
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteEqualityChain

/-!
# Integer translates of the actual Barnes logarithmic quotient

A fixed rational chart program returns the candidate name data and its
two logarithm bounds. For an arbitrary internal natural shift use the
actual recurrence at each translated chart. The finite named equality
chain reduces the iteration to quantifier-free induction on observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasIntegerPeriod

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCompactCutoffSplit (point_data_congr)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteEqualityChain (allSteps finite_cross)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev nameF (f : PR 2) : PR 2 := GaussianBarnesVignerasLogQuotient.nameF f

def advance (a b j : PTm n) : PTm n := a+j*b
def input (t : PTm 2) (a b : PTm n) : PTm n := fstT (inst2 t a b)
def margin (t : PTm 2) (a b : PTm n) : PTm n := fstT (sndT (inst2 t a b))
def bound (t : PTm 2) (a b : PTm n) : PTm n := sndT (sndT (inst2 t a b))
def data (t : PTm 2) (a b : PTm n) : PTm n :=
  GaussianBarnesVignerasLogQuotient.data a b (input t a b) (margin t a b)

def chart_step (f : PR 2) (t : PTm 2) (a b : PTm n) : Fm PTm n :=
  GaussianBarnesVignerasLogQuotient.source f a b (input t a b) (input t (a+b) b)
    (margin t a b) (bound t a b) (margin t (a+b) b) (bound t (a+b) b)

def source (f : PR 2) (t : PTm 2) (a b : PTm n) : Fm PTm n :=
  .all (chart_step f t (advance (Syn.shift a) (Syn.shift b) (var 0)) (Syn.shift b))

def body (t : PTm 2) : PTm 2 := data t (advance (fstT (var 1)) (sndT (var 1)) (var 0)) (sndT (var 1))

@[simp] theorem subst_advance {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    Syn.subst σ (advance a b j) = advance (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by simp [advance]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (a b : PTm n) :
    Syn.subst σ (data t a b) = data t (Syn.subst σ a) (Syn.subst σ b) := by simp [data,input,margin]

@[simp] theorem subst_chart_step {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (a b : PTm n) :
    (chart_step f t a b).subst σ = chart_step f t (Syn.subst σ a) (Syn.subst σ b) := by simp [chart_step,input,margin,bound]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (a b : PTm n) :
    (source f t a b).subst σ = source f t (Syn.subst σ a) (Syn.subst σ b) := by
  simp [source,Syn.subst_shift,Syn.shift_subst]

theorem chart_at (f : PR 2) (t : PTm 2) (a b j : PTm n) (h : Γ ⊢[PRAAx] source f t a b) :
    Γ ⊢[PRAAx] chart_step f t (advance a b j) b := by
  simpa only [source,subst_chart_step,subst_advance,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j

theorem body_at (t : PTm 2) (a b j : PTm n) : Γ ⊢[PRAAx] inst2 (body t) j (pairT a b) ≐ data t (advance a b j) b := by
  simp only [body,inst2,subst_data,subst_advance,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val]
  ipra_congr (data t (advance (var 0) (var 1) (var 2)) (var 1) : PTm 3) with [fst_pair a b,snd_pair a b,.eqRefl j]

private theorem body_regular (f : PR 2) (t : PTm 2) (a b j : PTm n) (h : Γ ⊢[PRAAx] source f t a b) :
    Γ ⊢[PRAAx] pointCN (nameF f) (inst2 (body t) j (pairT a b)) := by
  let v := advance a b j
  have hs := chart_at f t a b j h
  have reg := GaussianBarnesVignerasLogQuotient.regular f v b (input t v b) (margin t v b) (bound t v b)
    hs.andE₁.andE₁ hs.andE₁.andE₂ hs.andE₂.andE₁.andE₁
  exact point_data_congr (nameF f) _ _ (body_at t a b j).eqSymm reg

theorem steps (f : PR 2) (t : PTm 2) (a b : PTm n) (h : Γ ⊢[PRAAx] source f t a b) :
    Γ ⊢[PRAAx] allSteps (nameF f) (body t) (pairT a b) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let A := Syn.shift a
  let B := Syn.shift b
  let j : PTm (n+1) := var 0
  let v := advance A B j
  have hs : Δ ⊢[PRAAx] source f t A B := by simpa [Δ,A,B,Fm.shift,Syn.shift] using h.shift
  have c := chart_at f t A B j hs
  have unit := GaussianBarnesVignerasLogQuotient.unit_period f v B (input t v B) (input t (v+B) B)
    (margin t v B) (bound t v B) (margin t (v+B) B) (bound t (v+B) B) c
  have e : Δ ⊢[PRAAx] v+B ≐ advance A B (succ j) := by dsimp [v,advance]; ipra_ring
  have read : Δ ⊢[PRAAx] data t (v+B) B ≐ data t (advance A B (succ j)) B := by
    ipra_congr (data t (var 0) (var 1) : PTm 2) with [e,.eqRefl B]
  simpa only [A,B,j,Syn.shift,subst_pairT] using
    cross_data_congr (nameF f) (nameF f) _ _ _ _ (read.eqTrans (body_at t A B (succ j)).eqSymm)
      (body_at t A B j).eqSymm unit

theorem period_at (f : PR 2) (t : PTm 2) (a b j : PTm n) (h : Γ ⊢[PRAAx] source f t a b) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data t (advance a b j) b) (data t a b) := by
  have cross := finite_cross (nameF f) (body t) j (pairT a b) (steps f t a b h)
    (body_regular f t a b j h) (body_regular f t a b zero h)
  have e : Γ ⊢[PRAAx] advance a b zero ≐ a := by unfold advance; ipra_ring
  have last : Γ ⊢[PRAAx] data t (advance a b zero) b ≐ data t a b := by
    ipra_congr (data t (var 0) (var 1) : PTm 2) with [e,.eqRefl b]
  exact cross_data_congr _ _ _ _ _ _ (body_at t a b j) ((body_at t a b zero).eqTrans last) cross

theorem actual_Barnes_candidate_log_quotient_integer_period_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let a := var 0
       let b := var 1
       let j := var 2
       source f t a b ⟶ crossEquivalent (nameF f) (nameF f) (data t (advance a b j) b) (data t a b)) :=
  closeUniv 3 (.impI (period_at f t _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasIntegerPeriod
