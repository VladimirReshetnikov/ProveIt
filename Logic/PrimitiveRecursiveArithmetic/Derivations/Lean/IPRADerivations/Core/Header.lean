import IPRADerivations.Core.Basic

/-!
# The standard opens of a derivation module

Almost every module of the library begins with the same five `open` commands. `open_ipra` stands for them:

    open LeanProofs.ConciseIPRA LeanProofs.IPRA
    open LeanProofs.ConciseIPRA.Syn
    open scoped LeanProofs.ConciseIPRA.Fm
    open LeanProofs.ConciseIPRA.PTm (app zero succ)
    open LeanProofs.IPRA.PTm (num monus pred)

that is: the two root namespaces; the syntax operations (`Syn.shift`, `Syn.subst`, `Syn.inst`, …); the notation
for formulas and derivations (`≐`, `⟶`, `⋏`, `⋎`, `Γ ⊢[PRAAx] φ`); the term constructors `app`, `zero`, `succ`; and
the numerals, truncated subtraction and predecessor `num`, `monus`, `pred`. The names are absolute, so the command
can be used inside or outside a namespace. Opens that are specific to a module follow it as usual.
-/

set_option hygiene false in
/-- The standard opens of a derivation module (see the module documentation of `Core/Header`). -/
macro "open_ipra" : command => `(
  open LeanProofs.ConciseIPRA LeanProofs.IPRA
  open LeanProofs.ConciseIPRA.Syn
  open scoped LeanProofs.ConciseIPRA.Fm
  open LeanProofs.ConciseIPRA.PTm (app zero succ)
  open LeanProofs.IPRA.PTm (num monus pred))
