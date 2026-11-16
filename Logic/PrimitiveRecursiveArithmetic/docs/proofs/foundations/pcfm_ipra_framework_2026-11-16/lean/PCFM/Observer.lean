import IPRADerivations.Core.Search
import PCFM.Boolean

/-!
# Stable observer interfaces

This file defines the proof payloads.  Selection and erasure theorems are
planned against the checked bounded-search backend and are not assumed.
-/

namespace LeanProofs.IPRA.Framework

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ}

/-- A bounded witness relation, with the witness placed at variable `0`. -/
structure BoundedWitness (n : ℕ) where
  bound : PTm n
  good : Fm PTm (n + 1)
  goodQF : good.QF

/-- Put the distinguished witness in variable `0`, leaving two witness
slots followed by the original `n` parameters. -/
def witnessSubst0 : Fin (n + 1) → PTm (n + 2) :=
  Fin.cases (Syn.var 0) (fun i => Syn.var i.succ.succ)

/-- Put the distinguished witness in variable `1`. -/
def witnessSubst1 : Fin (n + 1) → PTm (n + 2) :=
  Fin.cases (Syn.var 1) (fun i => Syn.var i.succ.succ)

/-- Exact selection independence for a numerical observation term. -/
structure ExactObserver (W : BoundedWitness n) where
  obs : PTm (n + 1)
  stable :
    ([] : List (Fm PTm (n + 2))) ⊢[PRAAx]
      ((W.good.subst witnessSubst0 ⋏ W.good.subst witnessSubst1) ⟶
       (Syn.subst witnessSubst0 obs ≐ Syn.subst witnessSubst1 obs))

/-
Planned endpoints:

theorem select_least_good
  (W : BoundedWitness n)
  (nonempty : Γ |- [PRAAx] boundedExists W.good W.bound) :
  Γ |- [PRAAx] W.good[leastGood W / 0]

theorem ExactObserver.selection_independent
  (O : ExactObserver W) (nonempty : ...) :
  Γ |- [PRAAx] forallGood (fun z => O.obs z = O.obs (leastGood W))

Further files replace equality by a certified setoid relation or a rational
metric inequality.
-/

end LeanProofs.IPRA.Framework
