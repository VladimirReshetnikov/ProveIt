import IPRADerivations.Core.Integers

/-!
# The standard header of a derivation module

Almost every module of the library begins with the same five `open` commands and the same notation for the atoms
of a certificate. `open_ipra` stands for them:

    open LeanProofs.ConciseIPRA LeanProofs.IPRA
    open LeanProofs.ConciseIPRA.Syn
    open scoped LeanProofs.ConciseIPRA.Fm
    open LeanProofs.ConciseIPRA.PTm (app zero succ)
    open LeanProofs.IPRA.PTm (num monus pred)
    open scoped LeanProofs.IPRA.Atoms

that is: the two root namespaces; the syntax operations (`Syn.shift`, `Syn.subst`, `Syn.inst`, …); the notation
for formulas and derivations (`≐`, `⟶`, `⋏`, `⋎`, `Γ ⊢[PRAAx] φ`); the term constructors `app`, `zero`, `succ`;
the numerals, truncated subtraction and predecessor `num`, `monus`, `pred`; and `𝔞 t`, the term `t` as an element
of the ring of differences (the atoms of `linear_combination`, `ipra_lc` and `ipra_le` certificates). The names are
absolute, so the command can be used inside or outside a namespace. Opens that are specific to a module follow it
as usual. `open_ipra exports` does the same and also opens `LeanProofs.IPRA.Exports`, the exported helpers
described next.

`export_ipra NS (a b c)` makes the declarations `NS.a`, `NS.b`, `NS.c` of `LeanProofs.IPRA.NS` available under their
short names in every module that imports the exporting module and begins with `open_ipra exports`: they become
aliases in `LeanProofs.IPRA.Exports`. A module that begins with plain `open_ipra`, or with neither, is not affected.
The command is meant for helpers that many modules use: no `open NS (a b c)` line is needed for them any more. A
declaration of the module itself takes precedence over an exported name. An exported name and another opened
declaration with the same short name are told apart by their types where a term is expected, and are ambiguous in
`rw` and `simp` lists; so a short name should be exported only if no module that sees it uses the name for anything
else. The name of a structure, an inductive type or another namespace root is never exported: an alias of `X` does
not make `X.y` resolve, while `open NS (X)` does.
-/

namespace LeanProofs.IPRA.Atoms

/-- `𝔞 t`: the term `t` as an element of the ring of differences. The priority is low, so that a module may still
declare the same notation locally. -/
scoped notation (priority := low) "𝔞" t:max => LeanProofs.IPRA.Groth.ι (LeanProofs.IPRA.Q.mk _ t)

end LeanProofs.IPRA.Atoms

/-! The namespace of the exported short names: `export_ipra` fills it, `open_ipra exports` opens it. -/
namespace LeanProofs.IPRA.Exports
end LeanProofs.IPRA.Exports

/-- `open_ipra`: the standard opens of a derivation module; `open_ipra exports`: the same and the exported helpers
(see the module documentation of `Core/Header`). -/
syntax "open_ipra" (&" exports")? : command

set_option hygiene false in
macro_rules
  | `(open_ipra) => `(
      open LeanProofs.ConciseIPRA LeanProofs.IPRA
      open LeanProofs.ConciseIPRA.Syn
      open scoped LeanProofs.ConciseIPRA.Fm
      open LeanProofs.ConciseIPRA.PTm (app zero succ)
      open LeanProofs.IPRA.PTm (num monus pred)
      open scoped LeanProofs.IPRA.Atoms)
  | `(open_ipra exports) => `(
      open LeanProofs.ConciseIPRA LeanProofs.IPRA
      open LeanProofs.ConciseIPRA.Syn
      open scoped LeanProofs.ConciseIPRA.Fm
      open LeanProofs.ConciseIPRA.PTm (app zero succ)
      open LeanProofs.IPRA.PTm (num monus pred)
      open scoped LeanProofs.IPRA.Atoms
      open LeanProofs.IPRA.Exports)

open Lean Elab Command in
/-- `export_ipra NS (a b c)`: make `LeanProofs.IPRA.NS.a`, … available as `a`, … in every module that imports this
one and begins with `open_ipra exports` (see the module documentation of `Core/Header`). -/
elab "export_ipra " ns:ident "(" ids:ident+ ")" : command => do
  for id in ids do
    let full := `LeanProofs.IPRA ++ ns.getId ++ id.getId
    unless (← getEnv).contains full do
      throwErrorAt id "unknown declaration '{full}'"
    modifyEnv (addAlias · (`LeanProofs.IPRA.Exports ++ id.getId) full)
