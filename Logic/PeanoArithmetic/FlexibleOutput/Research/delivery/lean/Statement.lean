import Mathlib.Computability.PartrecCode
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Completeness.CounterModel
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# A concrete statement for a universal possible output at input zero

Source-reviewed against:
* ProveIt: 08edc6964d8990d2230179a9d65355ac1eee7a9e;
* Foundation: 32e1a0956a8622fad067328ca1959729a7634428;
* Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997;
* Lean: 4.32.0.

This file has NOT been compiled in the delivery environment. It defines
the concrete target and named intermediate obligations; it does not assert
that those obligations or the target have been proved. There are no axioms
or admitted proofs in this file.

The function in the intended statement is partial: its computation at zero
does not terminate in the standard natural numbers. The sentence evaluated
in another model is a fixed arithmetical formula for computation, not a Lean
equality between standard values.
-/

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol

abbrev Code := Nat.Partrec.Code

/-- The two inputs are a natural-number program code and its input.
`ofNatCode` is Mathlib's total decoding of its denumerable program type. -/
def universalEval : List.Vector ℕ 2 →. ℕ :=
  fun v => Nat.Partrec.Code.eval
    (Nat.Partrec.Code.ofNatCode (v.get 0)) (v.get 1)

/-- One fixed formula for the universal partial function.
Its variable order is output, program code, input.

`codeOfPartrec'` chooses one finite syntactic formula. That choice is made
once here, not afresh for each program. Standard correctness follows from
`codeOfPartrec'_spec` after proving `UniversalEvalPartrec` below. -/
noncomputable def universalGraph : ArithmeticSemisentence 3 :=
  codeOfPartrec' universalEval

/-- The arithmetic sentence saying that program `c` on input `x` outputs `y`.
The casts below are casts to closed arithmetic numeral terms, as in the
pinned Foundation substitution API. -/
noncomputable def haltSentence (c : Code) (x y : ℕ) : ArithmeticSentence :=
  universalGraph/[↑y, ↑(Encodable.encode c), ↑x]

/-- The requested corrected statement, using actual first-order models.
`Satisfiable` is Foundation's existing semantic model-existence predicate. -/
def MainClaim : Prop :=
  ∃ e : Code,
    ¬ (Nat.Partrec.Code.eval e 0).Dom ∧
    ∀ n : ℕ,
      LO.FirstOrder.Satisfiable (insert (haltSentence e 0 n) 𝗣𝗔)

/-- The construction can ignore its input, giving this stronger endpoint. -/
def StrongClaim : Prop :=
  ∃ e : Code,
    (∀ x : ℕ, ¬ (Nat.Partrec.Code.eval e x).Dom) ∧
    ∀ n : ℕ,
      LO.FirstOrder.Satisfiable (insert (haltSentence e 0 n) 𝗣𝗔)

/-! ## New obligations to discharge in the complete integration

These are definitions of propositions, not axioms or claimed theorems.
-/

/-- Obtain this from `eval_part`, computability of decoding, and projection. -/
def UniversalEvalPartrec : Prop := Nat.Partrec' universalEval

/-- Obtain this from `code_sigma_one`, unfolding the chosen compiler. -/
def UniversalGraphSigmaOne : Prop := Hierarchy 𝚺 1 universalGraph

/-- Specialization of the compiler's standard semantics, including the
round trip `ofNatCode (Encodable.encode c) = c`. -/
def StandardCorrectness : Prop :=
  ∀ (c : Code) (x y : ℕ),
    (ℕ↓[ℒₒᵣ] ⊧ haltSentence c x y) ↔
      y ∈ Nat.Partrec.Code.eval c x

/-- The forward finite-computation bridge required by the diagonal argument.
It follows from StandardCorrectness and Sigma-1 completeness of PA. -/
def FiniteProofAdequacy : Prop :=
  ∀ (c : Code) (x y : ℕ),
    y ∈ Nat.Partrec.Code.eval c x → 𝗣𝗔 ⊢ haltSentence c x y

/-- Effective enumeration of the refutations searched by the program.
Use one fixed formula above, computable numeral substitution, and the
recursively enumerable PA proof relation. -/
def RefutationsRE : Prop :=
  REPred (fun p : Code × ℕ => 𝗣𝗔 ⊢ ∼(haltSentence p.1 0 p.2))

/-- Internal determinism, including nonstandard program and input values.

This is a separate arithmetization obligation. In the pinned Foundation
Representation source, `code_uniq` occurs in a commented-out section and
is NOT an available theorem. Prove the corresponding compiler lemma, or
use a directly verified deterministic finite-computation formula.

Standard correctness alone does not imply this assertion. -/
def FunctionalityInPAModels : Prop :=
  ∀ (M : Type) [Nonempty M] [LO.ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
      (program input y z : M),
    (M ⊧/![y, program, input] universalGraph) →
    (M ⊧/![z, program, input] universalGraph) → y = z

/-- The concrete graph interpretation together with the main model claim.
This makes the arithmetization requirements explicit in the final goal. -/
def FullySpecifiedMainClaim : Prop :=
  StandardCorrectness ∧ FunctionalityInPAModels ∧ MainClaim

end PAFlexibleOutput
