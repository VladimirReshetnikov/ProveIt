import ConciseIPRA.PR
import PFIG.ExactCore

/-!
# Fixed PFIG syntax and two-pass compiler blueprint

`LocalProgram` is metasyntax elaborated to concrete `PR` terms.  The object
theory never evaluates an arbitrary code for a primitive-recursive program.
The first implementation may bypass this AST and generate specialized Lean
files; the structures below specify the eventual verified elaborator.
-/

namespace LeanProofs.ConciseIPRA.PFIG.Graph

open Syn
open scoped Fm

inductive NodeKind
  | exact
  | loop
  | search
  | relation
  | guard
  | observe
  | glue
  deriving DecidableEq, Repr

/-- A scalar request schema.  Tuple requests can later be encoded as naturals. -/
structure RequestSchema (n : Nat) where
  demand : PTm (n + 1)  -- requested output precision, parameters
  monotoneFormula : Fm PTm (n + 2)
  monotoneQF : monotoneFormula.QF

/-- A local node contract after its PR program has been specialized. -/
structure LocalContract (n : Nat) where
  pre : Fm PTm n
  post : Fm PTm n
  certificate : pre :: ([] : List (Fm PTm n)) ⊢[PRAAx] post

/-- Fixed graph node.  Dependencies must refer to earlier indices. -/
structure Node (n : Nat) where
  kind : NodeKind
  deps : List Nat
  depsEarlier : ∀ d ∈ deps, d < deps.length + 1  -- placeholder index invariant
  request : RequestSchema n
  local : LocalContract n

/-- A first implementation should replace `depsEarlier` with an indexed vector
or an explicit topological-order predicate over the complete node list. -/
structure PFIG (n : Nat) where
  nodes : List (Node n)
  input : Fm PTm n
  terminal : Fm PTm n

/-- Concrete two-pass compilation output. -/
structure Compiled (n : Nat) (G : PFIG n) where
  demandPost : Fm PTm n
  execPost : Fm PTm n
  demandProof : [G.input] ⊢[PRAAx] demandPost
  execProof : demandPost :: G.input :: [] ⊢[PRAAx] execPost
  extract : execPost :: demandPost :: G.input :: [] ⊢[PRAAx] G.terminal

/-- Soundness of an already compiled graph is just simultaneous cut. -/
theorem Compiled.sound {n : Nat} {G : PFIG n} (C : Compiled n G) :
    [G.input] ⊢[PRAAx] G.terminal := by
  have hExec : [G.input] ⊢[PRAAx] C.execPost := by
    apply C.execProof.trans
    intro A hA
    simp only [List.mem_cons, List.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact C.demandProof
    · exact Prf.hyp0
  apply C.extract.trans
  intro A hA
  simp only [List.mem_cons, List.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl
  · exact hExec
  · exact C.demandProof
  · exact Prf.hyp0

/-- Verified elaborator target. -/
def CompileTarget : Prop :=
  ∀ (n : Nat) (G : PFIG n), Nonempty (Compiled n G)

end LeanProofs.ConciseIPRA.PFIG.Graph
