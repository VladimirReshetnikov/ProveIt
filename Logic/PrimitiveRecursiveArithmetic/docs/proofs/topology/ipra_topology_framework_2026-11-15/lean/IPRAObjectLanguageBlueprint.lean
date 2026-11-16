import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language completion plan for the iPRA topology framework

This file records the exact endpoint in the current ProveIt API.  It is not
compiled in this delivery and contains `sorry` placeholders.  The target is
not a semantic theorem about `Nat`; the target is an inhabitant of

    Γ ⊢[PRAAx] φ

for each fixed finite algorithm and bounded formula.  Only after that proof is
constructed may `pra_iff_native.mp` transport it to the concise native core.
-/

namespace LeanProofs.ConciseIPRA.IPRATopology

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-! ## Fixed primitive-recursive symbols

Each item below is to be implemented as an explicit `PR k` syntax tree.  No
universal evaluator for arbitrary PR-code inputs is assumed.
-/

structure CodingSymbols where
  pair : PR 2
  left : PR 1
  right : PR 1
  bit : PR 2
  boundedUnion : PR 3
  boundedAll : PR 3
  boundedAny : PR 3
  boundedSearch : PR 3

/-- A compiled bounded formula: a fixed Boolean PR test and an object proof of equivalence. -/
structure Booleanized (n : Nat) where
  formula : Fm PTm n
  test : PR n
  accepts : Fm PTm n
  accepts_def : accepts = (PTm.app test Syn.var ≐ PTm.succ PTm.zero)
  equivalent : [] ⊢[PRAAx] Fm.iff formula accepts

/-- A fixed finite-complex presentation at the object level. -/
structure ComplexSymbols (n : Nat) where
  vertexBound : PR n
  simplex : PR (n + 1)       -- input parameters plus a bitset
  simplexDownward : Fm PTm n
  downwardProof : [] ⊢[PRAAx] simplexDownward

/-- A fixed carrier verifier and its internal correctness theorem. -/
structure CarrierSymbols (n : Nat) where
  source target : ComplexSymbols n
  cloud : PR (n + 2)         -- parameters, source vertex, target bitset output
  validFormula : Fm PTm n
  validProof : [] ⊢[PRAAx] validFormula
  leastSelection : PR (n + 1)
  selectionFormula : Fm PTm n
  selectionProof : [] ⊢[PRAAx] selectionFormula
  contiguousFormula : Fm PTm n
  contiguousProof : [] ⊢[PRAAx] contiguousFormula

/-- A bounded loop certificate in the actual object theory. -/
structure LoopCertificate (n : Nat) where
  invariant : Fm PTm (n + 1)
  invariantQF : invariant.QF
  base : [] ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : [invariant] ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (PTm.var 0)))

/-- Quantifier-free induction closes the bounded finite invariant. -/
theorem LoopCertificate.conclude {n : Nat} (C : LoopCertificate n) :
    [] ⊢[PRAAx] Fm.all C.invariant := by
  exact PRA.qfInd C.invariant C.invariantQF C.base (by simpa using C.step)

/-! ## Main object-theory targets

A metalevel compiler generates the following formulas from fixed finite syntax.
They are fields, rather than dummy definitions such as `Fm.top`, so an
unfinished formula cannot accidentally be mistaken for a proved theorem.
-/

structure TopologyFormulas (n : Nat) where
  carrierComposition : Fm PTm n
  selectionContiguity : Fm PTm n
  prismIdentity : Fm PTm n
  bettiCorrect : Fm PTm n
  finiteContinuity : Fm PTm n

structure TopologyObjectProofs {n : Nat} (F : TopologyFormulas n) where
  carrierComposition : [] ⊢[PRAAx] F.carrierComposition
  selectionContiguity : [] ⊢[PRAAx] F.selectionContiguity
  prismIdentity : [] ⊢[PRAAx] F.prismIdentity
  bettiCorrect : [] ⊢[PRAAx] F.bettiCorrect
  finiteContinuity : [] ⊢[PRAAx] F.finiteContinuity

/-- The existing bridge is applied only to an already constructed derivation. -/
theorem toNative {n : Nat} {φ : Fm PTm n} (h : [] ⊢[PRAAx] φ) :
    NPrf [] (NFm.ofPRA φ) := by
  simpa using (pra_iff_native.mp h)

/-!
## Dependency order for a complete implementation

1. Implement pairing, lists, bitsets, bounded folds, parity, and matrices as
   explicit `PR` trees; prove their defining equations using `PRA.proj`,
   `PRA.comp`, `PRA.precZero`, and `PRA.precSucc`.
2. Define a bounded-formula syntax and compile it to Boolean `PR` tests.
   Prove `Booleanized.equivalent` by syntax recursion; bounded quantifiers use
   object-level quantifier-free induction on their finite folds.
3. Encode complexes and carriers.  Prove downward closure, carrier composition,
   least-selection membership, and contiguity as bounded Boolean invariants.
4. Enumerate q-simplices by bounded search, define normalized images and the
   boundary/prism parity folds, and prove the prism identity by induction on
   simplex length and cancellation of adjacent terms.
5. Define Gaussian elimination over F_2 as a bounded state transition.  Use a
   `LoopCertificate` to prove preservation of row space and rank accounting.
6. Instantiate `TopologyObjectProofs`; only then use `toNative`.
7. For represented spaces, keep every evaluator fixed.  A theorem is a schema
   in the evaluator and its explicit modulus/refinement certificates, not a
   first-order quantification over arbitrary functions or spaces.
-/

end LeanProofs.ConciseIPRA.IPRATopology
