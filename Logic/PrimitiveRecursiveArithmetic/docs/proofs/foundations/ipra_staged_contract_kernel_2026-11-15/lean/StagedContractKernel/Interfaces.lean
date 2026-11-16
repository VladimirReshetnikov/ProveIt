import StagedContractKernel.Kernel

/-!
# Domain-facing obligation interfaces

These records are deliberately proof-bearing.  Filling one requires actual
`Prf PRAAx` terms.  They separate four public theorem classes: deterministic,
relational, stable-observable, and boundary-conditional statements.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace StagedContractKernel

open Syn
open scoped Fm

variable {n : Nat} {Gamma : List (Fm PTm n)}

/-- A deterministic finite producer followed by an object-theory verifier. -/
structure DeterministicContract
    (Pre Post : Fm PTm n) where
  output : PTm n
  correctness : Pre :: Gamma ⊢[PRAAx] Post

/-- A bounded relational producer: the public result is existential, while the
implementation carries a concrete selected witness and its proof. -/
structure WitnessContract
    (Relation : Fm PTm (n + 1)) where
  witness : PTm n
  witnessCorrect : Gamma ⊢[PRAAx] Relation.subst (inst witness)

namespace WitnessContract

theorem compile
    {Relation : Fm PTm (n + 1)}
    (W : WitnessContract (Gamma := Gamma) Relation) :
    Gamma ⊢[PRAAx] Fm.ex Relation :=
  existsFromWitness Relation W.witness W.witnessCorrect

end WitnessContract

/-- Two arbitrary certified branches suffice when the requested observation is
proved independent of their internal choices. -/
structure ExactObservationContract
    (First Second Observation : Fm PTm n) where
  first : Gamma ⊢[PRAAx] First
  second : Gamma ⊢[PRAAx] Second
  independence : First :: Second :: Gamma ⊢[PRAAx] Observation

namespace ExactObservationContract

theorem compile
    {First Second Observation : Fm PTm n}
    (C : ExactObservationContract (Gamma := Gamma)
      First Second Observation) :
    Gamma ⊢[PRAAx] Observation :=
  stableObservable First Second Observation C.first C.second C.independence

end ExactObservationContract

/-- A theorem whose missing global datum is visible in the statement. -/
structure ConditionalContract
    (Boundary Goal : Fm PTm n) where
  boundary : Gamma ⊢[PRAAx] Boundary
  reduction : Boundary :: Gamma ⊢[PRAAx] Goal

namespace ConditionalContract

theorem compile
    {Boundary Goal : Fm PTm n}
    (C : ConditionalContract (Gamma := Gamma) Boundary Goal) :
    Gamma ⊢[PRAAx] Goal :=
  withBoundary Boundary Goal C.boundary C.reduction

end ConditionalContract

/-- Exact recovery from an approximate branch requires a separation theorem. -/
structure GapContract
    (Approx Gap Exact : Fm PTm n) where
  approximation : Gamma ⊢[PRAAx] Approx
  gap : Gamma ⊢[PRAAx] Gap
  erase : Approx :: Gap :: Gamma ⊢[PRAAx] Exact

namespace GapContract

theorem compile
    {Approx Gap Exact : Fm PTm n}
    (C : GapContract (Gamma := Gamma) Approx Gap Exact) :
    Gamma ⊢[PRAAx] Exact :=
  exactFromGap Approx Gap Exact C.approximation C.gap C.erase

end GapContract

end StagedContractKernel
end LeanProofs.ConciseIPRA
