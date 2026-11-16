import KIFC.RelationalBlueprint

/-!
# Specialized graph compiler blueprint

The graph AST belongs to the metalevel.  A compiler should emit fixed `PR`
syntax and a `Schedule`; it should not define an object-level universal
interpreter.
-/

namespace LeanProofs.KIFC

open LeanProofs.ConciseIPRA
open scoped Fm

inductive NodeKind
  | algebra
  | boolean
  | search
  | loop
  | relation
  | observer
  deriving DecidableEq, Repr

/-- Minimal metalevel metadata.  The actual generator will also carry syntax
builders for terms/formulas and theorem constructors. -/
structure GraphNode where
  name : String
  kind : NodeKind
  dependencies : List Nat
  deriving Repr

/-- The kernel-facing result of compiling one fixed graph. -/
structure CompiledGraph (n : ℕ) where
  pre : List (Fm PTm n)
  post : Fm PTm n
  schedule : Schedule n pre post

namespace CompiledGraph

/-- Soundness is definitionally schedule compilation. -/
noncomputable def sound (g : CompiledGraph n) :
    g.pre ⊢[PRAAx] g.post :=
  g.schedule.compile

end CompiledGraph

/-!
The metalevel generator must check:

* dependency indices precede the node;
* generated term arities and variable layouts match;
* every local node constructor returns a `KernelRule` or intermediate theorem;
* all bounded loops have generated `LoopCertificate`s;
* relational nodes expose path-checker proofs rather than semantic lists;
* the emitted terminal object is `CompiledGraph`, so `sound` is automatic.
-/

end LeanProofs.KIFC
