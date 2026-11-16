import PA194ModelAdjunctiveTheory
import PA194ModelEmptyIrreflexive

/-!
# The source theory of the fixed set axioms, and its axiom rule

`fixedSetTheory` is the theory of the relational source language whose axioms are the five
equality axioms of `Theory.eqAxiom`, weak adjunction, the empty set and irreflexivity of
membership: every source axiom of the standard development that is a single sentence. It
has an explicit `Δ₁` presentation (a disjunction of eight equations).

* `fixedSetTheory_eq`: the theory is `adjunctiveTheory ∪ {sourceEmptySet, sourceIrreflexivity}`.
* `fixedSetTheory_class`: in a model, the internal axiom class is "one of the five quoted
  equality axioms, or one of the three quoted set axioms".
* `simRuleFixedSetAxiom`: the axiom field of a simulation for this theory, for the numerical
  calculus and the fixed formula translation, under the reserve bound `base + p ≤ reserve`.

The separation scheme is not in the theory. No simulation is constructed, and nothing here
yields a consistency implication.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol.Semiformula
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance fixedSetZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance fixedSetOne : One M := ⟨F oneCode Fin.elim0⟩
local instance fixedSetAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance fixedSetMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance fixedSetLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance fixedSetIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fixedSetList : List (Sentence M6.PA.RelationalSource.language) :=
  [sourceEqRefl,sourceEqSymm,sourceEqTrans,sourceEqRelExt,
    PA194RelExtTypedTranslation.sourceRelExt,sourceWeakAdjunction,sourceEmptySet,
    sourceIrreflexivity]

/-- The equality axioms of the relational source language together with weak adjunction,
the empty set and irreflexivity of membership. -/
def fixedSetTheory : Theory M6.PA.RelationalSource.language := {σ | σ ∈ fixedSetList}

theorem fixedSetTheory_eq :
    fixedSetTheory = adjunctiveTheory ∪ {sourceEmptySet,sourceIrreflexivity} := by
  ext σ
  simp only [fixedSetTheory,fixedSetList,adjunctiveTheory,adjunctiveList,Set.mem_setOf_eq,
    List.mem_cons,List.not_mem_nil,or_false,Set.mem_union,Set.mem_insert_iff,
    Set.mem_singleton_iff]
  tauto

def fixedSetTheoryFormula : 𝚺₀.Semisentence 1 := .mkSigma
  “x. x = ↑(Encodable.encode sourceEqRefl) ∨
    x = ↑(Encodable.encode sourceEqSymm) ∨ x = ↑(Encodable.encode sourceEqTrans) ∨
    x = ↑(Encodable.encode sourceEqRelExt) ∨
    x = ↑(Encodable.encode PA194RelExtTypedTranslation.sourceRelExt) ∨
    x = ↑(Encodable.encode sourceWeakAdjunction) ∨
    x = ↑(Encodable.encode sourceEmptySet) ∨
    x = ↑(Encodable.encode sourceIrreflexivity)”

@[implicit_reducible] noncomputable def fixedSetTheoryDelta : fixedSetTheory.Δ₁ where
  ch := .ofZero fixedSetTheoryFormula _
  mem_iff := by
    intro φ
    simp [fixedSetTheory, fixedSetTheoryFormula, fixedSetList, Semiformula.quote_eq_encode]
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

/-- The internal axiom class of the theory, in a model. -/
theorem fixedSetTheory_class (p : M) :
    letI := fixedSetTheoryDelta
    p ∈ fixedSetTheory.Δ₁Class ↔
      finiteEqAxiomCode p ∨ p = (⌜sourceWeakAdjunction⌝ : M) ∨
        p = (⌜sourceEmptySet⌝ : M) ∨ p = (⌜sourceIrreflexivity⌝ : M) := by
  letI := fixedSetTheoryDelta
  change M ⊧/![p] (fixedSetTheoryFormula.val) ↔ _
  simp [fixedSetTheoryFormula, finiteEqAxiomCode, Sentence.quote_eq_encode, numeral_eq_natCast,
    or_assoc]

/-- **The axiom field of a simulation for the theory of the fixed set axioms**, under the
single reserve bound used for the equality axioms. -/
theorem simRuleFixedSetAxiom (e p : M) (hz : simBase e + p ≤ simReserve e) :
    letI := fixedSetTheoryDelta
    p ∈ fixedSetTheory.Δ₁Class →
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1) := by
  letI := fixedSetTheoryDelta
  intro hax
  rcases (fixedSetTheory_class p).mp hax with h | h | h | h
  · have hrule := finiteEqTheory_axiom_rule e p hz
    exact hrule ((finiteEqTheory_class p).mpr h)
  · subst h
    exact simRuleWeakAdjunction e (weakAdjunction_reserve _ _ hz)
  · subst h
    exact simRuleEmptySet e
  · subst h
    exact simRuleIrreflexivity e

#print axioms fixedSetTheory_eq
#print axioms fixedSetTheoryDelta
#print axioms fixedSetTheory_class
#print axioms simRuleFixedSetAxiom
end models
end PA194ModelLogic
