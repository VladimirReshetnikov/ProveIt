import PA194CodeInstance
import PA194TermWellFormed

/-! Term-closing definability and preservation of well-formedness at arbitrary
model-internal terms.  The two projection-code certificates are retained; no
Σ₁-definability assumption on the closing operation is required. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194TermWellFormedUnconditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- One model-independent arithmetic formula defines the full three-input
term-closing function, for all inputs in every such model. -/
theorem close_graph [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1) :
    𝚺₁.DefinedFunction
      (fun e : Fin 3 → M => F (PA194TermRecursion.closeCode first second) e)
      (PA194CodeGraph.graph (PA194TermRecursion.closeCode first second)) :=
  PA194CodeGraph.modelGraph _

/-- The term-closing code has a Σ₁ graph for every fixed model-valued
label and binder depth; this requires no projection-code certificates. -/
theorem close_definable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1) (label depth : M) :
    𝚺₁-Function₁ (fun t : M => F (PA194TermRecursion.closeCode first second) ![t,label,depth]) :=
  PA194CodeInstance.unary_of_three _ label depth

/-- Closing a well-formed term preserves well-formedness, including for
nonstandard term codes.  `hf` and `hs` certify the pairing projections. -/
theorem internal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M) (t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    IsSemiterm ℒₒᵣ (depth + 1) (F (PA194TermRecursion.closeCode first second) ![t,label,depth]) :=
  PA194TermWellFormed.internal_of_function first second hf hs label depth
    (close_definable first second label depth) t ht


/-- A fixed pair of certified candidate-PRA projection codes. -/
noncomputable def canonicalFirst : Code 1 := Classical.choose PA194BranchSeed.PRA_has_pi1Code
noncomputable def canonicalSecond : Code 1 := Classical.choose PA194BranchSeed.PRA_has_pi2Code

/-- With the certified projection codes chosen once and for all, term closing
preserves well-formedness without any additional certificate hypotheses. -/
theorem canonical_internal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    IsSemiterm ℒₒᵣ (depth + 1)
      (F (PA194TermRecursion.closeCode canonicalFirst canonicalSecond) ![t,label,depth]) := by
  apply internal canonicalFirst canonicalSecond
  · exact (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
  · exact (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2
  · exact ht

#print axioms close_graph
#print axioms canonical_internal
#print axioms close_definable
#print axioms internal
end models
end PA194TermWellFormedUnconditional
