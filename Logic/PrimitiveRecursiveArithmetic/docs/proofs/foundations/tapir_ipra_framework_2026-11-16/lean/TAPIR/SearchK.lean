import IPRADerivations.Core.Search

/-!
# Arity-polymorphic bounded search (formalization blueprint)

The current checked `Search` module handles a body with one additional
parameter.  This file records the generic `k`-parameter construction described
in the report.  Every `sorry` is an explicit implementation milestone; no
claim is made that this file compiles.
-/

namespace LeanProofs.IPRA.TAPIR.SearchK

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {k n : ℕ} {Γ : List (Fm PTm n)}

/-- Rename body variables `0 = candidate`, `1..k = parameters` into step
variables `0 = stage`, `1 = accumulator`, `2.. = parameters`. -/
def liftBody (f : PTm (k + 1)) : PTm (k + 2) :=
  Syn.subst (Fin.cases (var 0) (fun j => var j.succ.succ)) f

/-- Step of least-zero search. -/
def muStep (f : PTm (k + 1)) : PTm (k + 2) :=
  var 1 + eqb (var 1) (var 0) * sg (liftBody f)

/-- `muF f (N, x_1, ..., x_k)`.  The base is the zero term of arity `k`. -/
def muF (f : PTm (k + 1)) : PR (k + 1) :=
  recDef (zero : PTm k) (muStep f)

/-- Application of the generic search symbol. -/
def mu (f : PTm (k + 1)) (N : PTm n) (xs : Fin k → PTm n) : PTm n :=
  app (muF f) (Fin.cases N xs)

/-- Body application at a candidate and parameter vector. -/
def body (f : PTm (k + 1)) (i : PTm n) (xs : Fin k → PTm n) : PTm n :=
  Syn.subst (Fin.cases i xs) f

@[simp] theorem subst_body {m : ℕ} (σ : Fin n → PTm m)
    (f : PTm (k + 1)) (i : PTm n) (xs : Fin k → PTm n) :
    Syn.subst σ (body f i xs) = body f (Syn.subst σ i) (fun j => Syn.subst σ (xs j)) := by
  unfold body
  rw [Syn.subst_subst]
  congr 1
  funext j
  refine Fin.cases ?_ (fun l => ?_) j <;> simp

/-- Generic zero equation. -/
theorem mu_zero (f : PTm (k + 1)) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] mu f zero xs ≐ zero := by
  sorry

/-- Generic successor equation. -/
theorem mu_succ (f : PTm (k + 1)) (N : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] mu f (succ N) xs ≐
      mu f N xs + eqb (mu f N xs) N * sg (body f N xs) := by
  sorry

/-- Search invariant: bound, success, and minimality. -/
theorem search_spec (f : PTm (k + 1)) (N i : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx]
      le (mu f N xs) N ⋏
      ((lt (mu f N xs) N ⟶ body f (mu f N xs) xs ≐ zero) ⋏
       (lt i (mu f N xs) ⟶ neg (body f i xs ≐ zero))) := by
  /-
  Port `Core/Search.spec_open` with `N`, `i`, and the `k` parameters free.
  Use one `PRA.qfInd`/`IPRA.ind` on `N`; the mathematical branches are
  identical to the checked one-parameter proof.
  -/
  sorry

 theorem search_minimal (f : PTm (k + 1)) {N i : PTm n}
    {xs : Fin k → PTm n}
    (h : Γ ⊢[PRAAx] lt i (mu f N xs)) :
    Γ ⊢[PRAAx] neg (body f i xs ≐ zero) := by
  exact Prf.impE (Prf.andE₂ (Prf.andE₂ (search_spec f N i xs))) h

 theorem search_found (f : PTm (k + 1)) {N i : PTm n}
    {xs : Fin k → PTm n}
    (hf : Γ ⊢[PRAAx] body f i xs ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx]
      lt (mu f N xs) N ⋏
      ((body f (mu f N xs) xs ≐ zero) ⋏ le (mu f N xs) i) := by
  sorry

end LeanProofs.IPRA.TAPIR.SearchK
