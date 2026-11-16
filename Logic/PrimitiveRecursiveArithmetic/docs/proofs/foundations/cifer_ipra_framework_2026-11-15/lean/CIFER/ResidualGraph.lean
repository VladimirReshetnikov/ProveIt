import Std

/-!
# Host-level residual graph normalization

The finite graph in this file is metadata, not an encoded universal evaluator
inside iPRA.  It is specialized by Lean before object-language terms and proofs
are constructed.  This is how CIFER avoids assuming a total primitive-
recursive evaluator for arbitrary program codes.

The executable definitions below are intentionally conservative.  The main
formalization task is to connect their output to `CIFER.ResidualBuild` in
`ObjectCompiler.lean`.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CIFER

inductive NodeKind where
  | input
  | local
  | boundary
  | final
  deriving Repr, DecidableEq, Inhabited

structure GNode where
  name : String
  kind : NodeKind
  deps : List Nat
  deriving Repr, DecidableEq, Inhabited

abbrev Graph := Array GNode

/-- Every dependency of node `i` points to an earlier node. -/
def Topological (g : Graph) : Prop :=
  forall i (hi : i < g.size) j, j ∈ (g[i]'hi).deps -> j < i

/-- One backwards expansion step on a Boolean reachability table. -/
def reachStep (g : Graph) (marked : Array Bool) : Array Bool :=
  Id.run do
    let mut out := marked
    for i in [:g.size] do
      if marked.getD i false then
        for j in (g.getD i default).deps do
          if j < out.size then
            out := out.set! j true
    return out

/--
Reachability from a target after `g.size` backwards sweeps.  On a topological
graph one sweep in descending order would suffice; repeated sweeps keep the
reference definition independent of traversal details.
-/
def reachable (g : Graph) (target : Nat) : Array Bool :=
  let seed := Array.ofFn (fun i : Fin g.size => i.1 == target)
  Nat.rec seed (fun _ acc => reachStep g acc) g.size

/-- Primitive unresolved leaves reachable from the selected target. -/
def residualIds (g : Graph) (target : Nat) : List Nat :=
  let r := reachable g target
  (List.range g.size).filter fun i =>
    r.getD i false && (g.getD i default).kind == .boundary

/-- Duplicate-free formulas are attached later by the object compiler. -/
def residualNames (g : Graph) (target : Nat) : List String :=
  (residualIds g target).map fun i => (g.getD i default).name

/-!
Completion targets, in dependency order:

1. `reachable_correct`: on `Topological g`, `reachable g t` marks exactly the
   reflexive transitive dependency closure of `t`.
2. `residual_characterization`: `residualIds` is exactly the set of reachable
   primitive boundary leaves.
3. `compile_sound`: after attaching a formula and local `Prf PRAAx`
   constructor to every node, the topological fold returns
   `ResidualBuild Gamma residual targetPrefix`.
4. `supply_sound`: use `ResidualBuild.close` to discharge a supplied proof of
   each residual formula.

The paper proves the mathematical induction behind these targets.  They are
not asserted here as axioms or admitted theorems.
-/

end LeanProofs.ConciseIPRA.CIFER
